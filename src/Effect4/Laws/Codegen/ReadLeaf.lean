import Effect4.Codegen.Read
import Effect4.Laws.Codegen.Record
import Effect4.Laws.Codegen.Tuple
import Effect4.Laws.Codegen.Classes
import Effect4.Laws.Codegen.ListFold

/-!
# Leaf and row reconstruction laws

Concept: Exact Codecs & Data Plane Embeddings. Claim served: `printed-modules` (R2/R3).
The term retraction keeps scope as its premise, and, since the payload class face (decisions row
120, part E2), coverage: the module's classes declare every class construction's fields
(`Term.covers`). Since the list fold (decisions row 228) it also takes a term that states no
accumulator type (`Term.unannotated`): a stated type is printed and not read. Exactness assumes successful reading under any classes. These declarations moved
from the core reader so record cases can use the Laws graph. Names and namespaces remain
unchanged. No target execution or host equivalence is claimed. The placement and consumers are in
the record-wrapper brief.
-/

set_option autoImplicit false

namespace Effect4.Program
open TypeScript (Expr)
variable {Op : Type}

/-! ## Receipts: what the reader needs of `Except` -/

@[simp] theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

@[simp] theorem map_ok {ε α β : Type} (f : α → β) (a : α) :
    (Except.ok a : Except ε α).map f = .ok (f a) := rfl

theorem bind_eq_ok {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β} :
    (m >>= f) = .ok b ↔ ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m <;> simp [Bind.bind, Except.bind]

theorem map_eq_ok {ε α β : Type} {m : Except ε α} {f : α → β} {b : β} :
    m.map f = .ok b ↔ ∃ a, m = .ok a ∧ f a = b := by
  cases m <;> simp [Except.map]

/-! ## Binders are injective

`Var.name i = "a" ++ Nat.repr i`, and `Nat.repr` is `String.ofList` of the decimal digits.
The string layer's injectivity lemmas reach `Classical.choice` on this toolchain (they go
through `String.toList`), so injectivity is taken from the bytes instead: the UTF-8 bytes of
a decimal string are its digits, and `decodeBytes` reads the number back. -/

theorem decodeBytes_append (bs : List UInt8) (b : UInt8) :
    decodeBytes (bs ++ [b]) = decodeBytes bs * 10 + digitOfByte b :=
  Data.NatDecimal.decodeBytes_append bs b

theorem utf8_digitChar : ∀ m, m < 10 →
    String.utf8EncodeChar (Nat.digitChar m) = [UInt8.ofNat (48 + m)] :=
  Data.NatDecimal.utf8_digitChar

theorem digitOfByte_digit : ∀ m, m < 10 → digitOfByte (UInt8.ofNat (48 + m)) = m :=
  Data.NatDecimal.digitOfByte_digit

theorem toDigitsCore_append (fuel : Nat) : ∀ (n : Nat) (ds : List Char), n < fuel →
    Nat.toDigitsCore 10 fuel n ds = Nat.toDigitsCore 10 fuel n [] ++ ds :=
  Data.NatDecimal.toDigitsCore_append fuel

theorem decodeBytes_toDigitsCore (fuel : Nat) : ∀ n, n < fuel →
    decodeBytes ((Nat.toDigitsCore 10 fuel n []).flatMap String.utf8EncodeChar) = n :=
  Data.NatDecimal.decodeBytes_toDigitsCore fuel

theorem decodeBytes_repr (n : Nat) : decodeBytes (Nat.repr n).toByteArray.data.toList = n :=
  Data.NatDecimal.decodeBytes_repr n

theorem readKey_exact {Op : Type} {sig : Signature Op} {x : Expr} {key : ServiceKey}
    (h : readKey sig x = .ok key) : printKey sig key = .ok x := by
  unfold readKey at h
  split at h
  · split at h
    · rename_i heq
      cases h
      subst heq
      simp only [printKey, if_true]
    · cases h
  · dsimp only at h
    split at h
    · rename_i heq
      cases h
      simp only [printKey, if_neg heq.1, heq.2.2.1, ok_bind, heq.2.1,
        ← heq.2.2.2]
    · cases h
  · dsimp only at h
    split at h
    · rename_i ty hty
      split at h
      · rename_i heq
        cases h
        simp only [printKey, if_neg heq.1, hty, heq.2.2.2.1, ok_bind,
          heq.2.1, heq.2.2.1, ← heq.2.2.2.2]
      · cases h
    · cases h
  · cases h

private theorem repr_no_separator (n : Nat) :
    ∀ b ∈ (Nat.repr n).toByteArray.data.toList, (b != (95 : UInt8)) = true := by
  rw [Nat.repr, String.toByteArray_ofList, List.utf8Encode, List.toList_data_toByteArray,
    Nat.toDigits]
  suffices h : ∀ fuel n ds, n < fuel →
      (∀ c ∈ ds, ∀ b ∈ String.utf8EncodeChar c, (b != (95 : UInt8)) = true) →
      ∀ b ∈ (Nat.toDigitsCore 10 fuel n ds).flatMap String.utf8EncodeChar,
        (b != (95 : UInt8)) = true from h (n + 1) n [] (Nat.lt_succ_self n) (by simp)
  intro fuel
  induction fuel with
  | zero => intro n ds h; omega
  | succ fuel ih =>
    intro n ds hn hds
    have hm : n % 10 < 10 := Nat.mod_lt _ (by decide)
    have hd : ∀ b ∈ String.utf8EncodeChar (Nat.digitChar (n % 10)),
        (b != (95 : UInt8)) = true := by
      rw [utf8_digitChar _ hm]
      have : ∀ m, m < 10 → ((UInt8.ofNat (48 + m)) != (95 : UInt8)) = true := by decide
      simp only [List.mem_singleton]
      intro b hb
      subst b
      exact this _ hm
    have hcons : ∀ c ∈ Nat.digitChar (n % 10) :: ds,
        ∀ b ∈ String.utf8EncodeChar c, (b != (95 : UInt8)) = true := by
      intro c hc
      cases List.mem_cons.mp hc with
      | inl h => subst c; exact hd
      | inr h => exact hds c h
    rw [Nat.toDigitsCore]
    split
    · intro b hb
      obtain ⟨c, hc, hb⟩ := List.mem_flatMap.mp hb
      exact hcons c hc b hb
    · exact ih (n / 10) _ (by omega) hcons

private theorem split_separator (xs ys : List UInt8)
    (h : ∀ b ∈ xs, (b != (95 : UInt8)) = true) :
    (xs ++ 95 :: ys).takeWhile (· != 95) = xs ∧
      (xs ++ 95 :: ys).dropWhile (· != 95) = 95 :: ys := by
  induction xs with
  | nil => simp
  | cons b bs ih =>
    have hb := h b (List.mem_cons_self)
    have hbs : ∀ c ∈ bs, (c != (95 : UInt8)) = true :=
      fun c hc => h c (List.mem_cons_of_mem b hc)
    simp only [List.cons_append, List.takeWhile_cons, List.dropWhile_cons,
      hb, if_true, (ih hbs).1, (ih hbs).2, and_self]

theorem keyFromText_print (name service : Nat) :
    keyFromText ("k" ++ toString name ++ "_" ++ toString service) = ⟨⟨name⟩, ⟨service⟩⟩ := by
  have hk : "k".toByteArray.data.toList = [107] := by decide
  have hs : "_".toByteArray.data.toList = [95] := by decide
  simp only [keyFromText, String.toByteArray_append, ByteArray.data_append,
    Array.toList_append, hk, hs, List.append_assoc, List.cons_append,
    List.nil_append, List.drop_succ_cons, List.drop_zero]
  change ServiceKey.mk
    ⟨decodeBytes (((Nat.repr name).toByteArray.data.toList ++
      95 :: (Nat.repr service).toByteArray.data.toList).takeWhile (· != 95))⟩
    ⟨decodeBytes ((((Nat.repr name).toByteArray.data.toList ++
      95 :: (Nat.repr service).toByteArray.data.toList).dropWhile (· != 95)).drop 1)⟩ = _
  rw [(split_separator _ _ (repr_no_separator name)).1,
    (split_separator _ _ (repr_no_separator name)).2]
  simp only [List.drop_succ_cons, List.drop_zero, decodeBytes_repr]

/-- Full key text is injective because its decoder is a left inverse. Helper for
`keyIdentifier_injective`, the generated requirement identity claim (R5/R8). -/
theorem keyText_injective : Function.Injective keyText := by
  intro a b h
  have decoded := congrArg keyFromText h
  rcases a with ⟨⟨an⟩, ⟨asvc⟩⟩
  rcases b with ⟨⟨bn⟩, ⟨bt⟩⟩
  simpa only [keyText, keyFromText_print] using decoded

/-- At one fixed signature's scope identity, different keys have different target
Identifier syntax, independently of their carriers. This is a syntax theorem; the
pinned TypeScript assignment controls separately test the target interpretation. -/
theorem keyIdentifier_injective (scopeKey : ServiceKey) :
    Function.Injective (keyIdentifier scopeKey) := by
  intro a b h
  by_cases ha : a = scopeKey
  · by_cases hb : b = scopeKey
    · exact ha.trans hb.symm
    · simp only [keyIdentifier, if_pos ha, if_neg hb] at h
      cases h
  · by_cases hb : b = scopeKey
    · simp only [keyIdentifier, if_neg ha, if_pos hb] at h
      cases h
    · simp only [keyIdentifier, if_neg ha, if_neg hb, TypeScript.TypeRef.literal.injEq] at h
      exact keyText_injective h

/-- The successful structural key image reads back. Unsupported legacy type text
now refuses printing, so success is explicit instead of assuming a total string printer. -/
theorem readKey_printKey {Op : Type} (sig : Signature Op) (key : ServiceKey)
    {x : Expr} (hp : printKey sig key = .ok x) : readKey sig x = .ok key := by
  by_cases hs : key = sig.scopeKey
  · subst key
    simp only [printKey, if_true, Except.ok.injEq] at hp
    subst x
    simp only [readKey, if_true]
  · obtain ⟨⟨name⟩, ⟨service⟩⟩ := key
    cases ht : sig.serviceTy ⟨⟨name⟩, ⟨service⟩⟩ with
    | none =>
      simp only [printKey, if_neg hs, ht, ok_bind, Except.ok.injEq] at hp
      subst x
      simp only [readKey, keyText, keyFromText_print, ht, and_self, and_true, if_pos hs]
    | some ty =>
      cases hty : Effect4.Codegen.Types.ofTy ty with
      | none => simp only [printKey, if_neg hs, ht, hty, bind, Except.bind] at hp; cases hp
      | some target =>
        simp only [printKey, if_neg hs, ht, hty, ok_bind, Except.ok.injEq] at hp
        subst x
        simp only [readKey, keyText, keyFromText_print, ht, hty, and_self, and_true, if_pos hs]

theorem printKey_readable (sig : Signature Op) (key : ServiceKey)
    (hr : keyReadable sig key = true) : ∃ x, printKey sig key = .ok x := by
  by_cases hs : key = sig.scopeKey
  · exact ⟨.ident "Scope.Scope", by simp only [printKey, if_pos hs]⟩
  · cases ht : sig.serviceTy key with
    | none => exact ⟨_, by simp only [printKey, if_neg hs, ht, ok_bind]; rfl⟩
    | some ty =>
      simp only [keyReadable, ht, Option.isSome_iff_exists] at hr
      obtain ⟨target, htarget⟩ := hr
      exact ⟨_, by simp only [printKey, if_neg hs, ht, htarget, ok_bind]; rfl⟩

theorem repr_inj {a b : Nat} (h : Nat.repr a = Nat.repr b) : a = b := by
  have := congrArg (fun s => decodeBytes s.toByteArray.data.toList) h
  simpa [decodeBytes_repr] using this

theorem Var.name_inj {i j : Nat} (h : Var.name i = Var.name j) : i = j :=
  repr_inj (String.append_right_inj _ |>.mp h)

theorem Var.name_head (i : Nat) : (Var.name i).toByteArray.data.toList.head? = some 97 := by
  have ha : "a".toByteArray.data.toList = [97] := by decide
  rw [Var.name, String.toByteArray_append, ByteArray.data_append, Array.toList_append, ha]
  rfl

/-- A string whose first byte is not `'a'` is no binder name. -/
theorem Var.name_ne {s : String} (hs : s.toByteArray.data.toList.head? ≠ some 97) (i : Nat) :
    Var.name i ≠ s := fun h => hs (h ▸ Var.name_head i)

theorem Var.name_ne_undefined (i : Nat) : Var.name i ≠ "undefined" := Var.name_ne (by decide) i

theorem Var.name_ne_fiberId (i : Nat) : Var.name i ≠ "Effect.fiberId" :=
  Var.name_ne (by decide) i

theorem Var.read_exact : ∀ {n : Nat} {s : String} {i : Nat},
    Var.read n s = some i → s = Var.name i ∧ i < n
  | 0, _, _, h => by simp [Var.read] at h
  | n + 1, s, i, h => by
    simp only [Var.read] at h
    split at h
    · rename_i heq; cases h; exact ⟨heq.symm, Nat.lt_succ_self _⟩
    · obtain ⟨hs, hi⟩ := Var.read_exact h; exact ⟨hs, Nat.lt_succ_of_lt hi⟩

theorem Var.read_name : ∀ {n i : Nat}, i < n → Var.read n (Var.name i) = some i
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h => by
    simp only [Var.read]
    split
    · rename_i heq; rw [Var.name_inj heq]
    · rename_i hne
      have : i ≠ n := fun e => hne (by rw [e])
      exact Var.read_name (by omega)

theorem Var.read_none : ∀ {n : Nat} {s : String}, (∀ i, Var.name i ≠ s) → Var.read n s = none
  | 0, _, _ => rfl
  | n + 1, s, h => by simp only [Var.read]; rw [if_neg (h n)]; exact Var.read_none h

/-! ## Terms round-trip -/

open Effect4.Codegen.Classes (Classes)

/-- A term prints to no function: a list fold's step is the only function in a term's image, and
it is an argument of the fold's call. Step of the `app` case of `readTerm_printTerm`. -/
theorem binders_read_printTerm {n m : Nat} {bs : List Nat} (t : Term) :
    Effect4.Codegen.Binders.read m bs (printTerm n t) = none := by
  cases t with
  | var _ => rfl
  | lit v => cases v <;> rfl
  | app _ _ => rfl
  | record fields names values =>
    simp only [printTerm]
    split
    · rfl
    · simp only [Effect4.Codegen.Record.writeRecord]
      split <;> rfl
  | field _ _ _ => rfl
  | recordSet _ _ _ => rfl
  | tupleAt _ _ => rfl
  | fold _ _ _ _ => rfl

/-- An atom application is no list fold, whatever its name: where its image has three
arguments, the third is a term's image, and that is no function. Step of the `app` case of
`readTerm_printTerm`. -/
theorem listFold_read_app {n : Nat} (atom : String) (args : Terms) :
    Effect4.Codegen.ListFold.read n (.call (.ident atom) (printTerms n args)) = none := by
  match args with
  | .nil => rfl
  | .cons _ .nil => rfl
  | .cons _ (.cons _ .nil) => rfl
  | .cons _ (.cons _ (.cons c .nil)) =>
    simp only [printTerms, Effect4.Codegen.ListFold.read, binders_read_printTerm c,
      Option.map_none, ite_self]
  | .cons _ (.cons _ (.cons _ (.cons _ _))) => rfl

mutual
  /-- **The term round trip** (`collection-term-print-read`): a scoped term whose class
  constructions the classes cover reads back from its printing. Since decisions row 120, part E2,
  a class construction prints as `new Tag({ … })` and reads back from the module's classes, with
  `_tag` restored first (`Classes.classTag?`); placed at R8 (`translation-simulation`) as a step of
  `read_print`, and at R3 as the record terms' printed form. -/
  theorem readTerm_printTerm {classes : Classes} {n : Nat} (t : Term)
      (h : Term.scoped n t = true) (hc : t.covers classes = true)
      (hu : t.unannotated = true) :
      readTerm classes n (printTerm n t) = .ok t :=
    match t, h, hc, hu with
    | .var i, h, _, _ => by
      simp only [Term.scoped, decide_eq_true_eq] at h
      simp only [printTerm, readTerm, Effect4.Codegen.Classes.readClass,
        Effect4.Codegen.Record.readRecord, Effect4.Codegen.Record.readField,
        Effect4.Codegen.Record.readSet, Effect4.Codegen.Tuple.readAt,
        Effect4.Codegen.ListFold.read, Var.read_name h]
    | .lit .unit, _, _, _ => by
      simp only [printTerm, printLit, readTerm, Effect4.Codegen.Classes.readClass,
        Effect4.Codegen.Record.readRecord, Effect4.Codegen.Record.readField,
        Effect4.Codegen.Record.readSet, Effect4.Codegen.Tuple.readAt,
        Effect4.Codegen.ListFold.read, Var.read_none Var.name_ne_undefined, ↓reduceIte]
    | .lit (.nat k), _, _, _ => by
      rw [printTerm, printLit, readTerm]
      rfl
    | .lit (.bool b), _, _, _ => by rw [printTerm, printLit, readTerm]; rfl
    | .lit (.str s), _, _, _ => by rw [printTerm, printLit, readTerm]; rfl
    | .app atom args, h, hc, hu => by
      simp only [Term.scoped] at h
      rw [Term.covers_app] at hc
      rw [Term.unannotated_app] at hu
      rw [printTerm, readTerm]
      simp only [Effect4.Codegen.Classes.readClass,
        Effect4.Codegen.Record.readRecord, Effect4.Codegen.Record.readField,
        Effect4.Codegen.Record.readSet, Effect4.Codegen.Tuple.readAt]
      -- an atom application is no fold, whatever its name
      split
      · next list init body hl =>
        rw [listFold_read_app] at hl
        exact nomatch hl
      · rw [readTerms_printTerms args h hc hu]
        rfl
    | .record fields names values, h, hc, hu => by
      simp only [Term.scoped] at h
      rw [Term.covers_record, Bool.and_eq_true] at hc
      rw [Term.unannotated_record] at hu
      obtain ⟨hnode, hvals⟩ := hc
      have hr := readTerms_printTerms values h hvals hu
      rw [printTerm]
      cases hct : Effect4.Codegen.Classes.classTag? fields names values with
      | some tag =>
        obtain ⟨_, _, hnames, hvalues, _, hlen⟩ := Effect4.Codegen.Classes.classTag?_some hct
        have hlookup := coverNode_class hnode hct
        have htail : readTerms classes n (printTerms n (Effect4.Codegen.Classes.restTerms values)) =
            .ok (Effect4.Codegen.Classes.restTerms values) := by
          rw [hvalues] at hr
          simp only [printTerms, readTerms, bind_eq_ok] at hr
          obtain ⟨t', _, ts', hts', hcons⟩ := hr
          simp only [Except.ok.injEq, Terms.cons.injEq] at hcons
          rw [hcons.2] at hts'
          exact hts'
        have hlen' : names.tail.length = (printTerms n values).tail.length := by
          rw [Effect4.Codegen.Classes.printTerms_restTerms,
            Effect4.Codegen.Classes.printTerms_length, hlen]
        have hw := Effect4.Codegen.Classes.readClass_writeClass tag names.tail _ hlen'
        dsimp only
        rw [readTerm]
        split
        · next tag' names' values' hcls =>
          rw [hw] at hcls
          simp only [Option.some.injEq, Prod.mk.injEq] at hcls
          obtain ⟨rfl, rfl, rfl⟩ := hcls
          rw [hlookup]
          dsimp only
          rw [Effect4.Codegen.Classes.printTerms_restTerms, htail, ok_bind, ← hnames, ← hvalues,
            hct]
          exact if_pos rfl
        · next hcls => rw [hw] at hcls; exact nomatch hcls
      | none =>
        dsimp only
        rw [readTerm]
        split
        · next tag' names' values' hcls =>
          rw [Effect4.Codegen.Classes.readClass_writeRecord] at hcls
          exact nomatch hcls
        · have hs := Effect4.Codegen.Record.readRecord_writeRecord fields names (printTerms n values)
          split
          · next fields' names' values' hrec =>
            rw [hrec] at hs
            cases hs
            rw [hr, ok_bind, hct]
            rfl
          · next hrec => rw [hrec] at hs; exact nomatch hs
    | .field mode target name, h, hc, hu => by
      simp only [Term.scoped] at h
      rw [Term.covers_field] at hc
      rw [Term.unannotated_field] at hu
      rw [printTerm, readTerm]
      split
      · next tag' names' values' hcls =>
        rw [Effect4.Codegen.Classes.readClass_writeField] at hcls; exact nomatch hcls
      · have hr0 := Effect4.Codegen.Record.readRecord_writeField
          (decide (mode = .optional)) name (printTerm n target)
        split
        · next fields names values hr => rw [hr] at hr0; exact nomatch hr0
        ·
          have hs := Effect4.Codegen.Record.readField_writeField
            (decide (mode = .optional)) name (printTerm n target)
          split
          · next optional name' target' hf =>
            rw [hf] at hs
            cases hs
            rw [readTerm_printTerm target h hc hu]
            cases mode <;> rfl
          · next hf => rw [hf] at hs; exact nomatch hs
    | .recordSet target name value, h, hc, hu => by
      simp only [Term.scoped, Bool.and_eq_true] at h
      rw [Term.covers_recordSet, Bool.and_eq_true] at hc
      rw [Term.unannotated_recordSet, Bool.and_eq_true] at hu
      rw [printTerm, readTerm]
      split
      · next tag' names' values' hcls =>
        rw [Effect4.Codegen.Classes.readClass_writeSet] at hcls; exact nomatch hcls
      · simp only [Effect4.Codegen.Record.readRecord_writeSet,
          Effect4.Codegen.Record.readField_writeSet]
        have hs := Effect4.Codegen.Record.readSet_writeSet name (printTerm n target) (printTerm n value)
        split
        · next name' target' value' hr =>
          rw [hr] at hs
          cases hs
          rw [readTerm_printTerm target h.1 hc.1 hu.1]
          simp only [ok_bind, readTerm_printTerm value h.2 hc.2 hu.2]
        · next hr => rw [hr] at hs; exact nomatch hs
    | .tupleAt target index, h, hc, hu => by
      simp only [Term.scoped] at h
      rw [Term.covers_tupleAt] at hc
      rw [Term.unannotated_tupleAt] at hu
      rw [printTerm, readTerm]
      split
      · next tag' names' values' hcls =>
        rw [Effect4.Codegen.Classes.readClass_writeAt] at hcls; exact nomatch hcls
      · simp only [Effect4.Codegen.Tuple.readRecord_writeAt,
          Effect4.Codegen.Tuple.readField_writeAt, Effect4.Codegen.Tuple.readSet_writeAt]
        have hs := Effect4.Codegen.Tuple.readAt_writeAt index (printTerm n target)
        split
        · next index' target' hr =>
          rw [hr] at hs
          cases hs
          rw [readTerm_printTerm target h hc hu]
          rfl
        · next hr => rw [hr] at hs; exact nomatch hs
    -- the fold with no stated type: its image is none of the earlier readers', and its own
    -- reader returns the three printed parts, the body's two levels up
    | .fold accTy list init body, h, hc, hu => by
      simp only [Term.scoped, Bool.and_eq_true] at h
      rw [Term.covers_fold, Bool.and_eq_true, Bool.and_eq_true] at hc
      rw [Term.unannotated_fold, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
        Option.isNone_iff_eq_none] at hu
      obtain ⟨rfl, hul, hui, hub⟩ := hu
      rw [printTerm, Option.map_none, readTerm]
      split
      · next tag' names' values' hcls =>
        rw [Effect4.Codegen.ListFold.readClass_write] at hcls; exact nomatch hcls
      · simp only [Effect4.Codegen.ListFold.readRecord_write,
          Effect4.Codegen.ListFold.readField_write, Effect4.Codegen.ListFold.readSet_write,
          Effect4.Codegen.ListFold.readAt_write]
        have hs := Effect4.Codegen.ListFold.read_write n (printTerm n list) (printTerm n init)
          (printTerm (n + 2) body)
        split
        · next list' init' body' hr =>
          rw [hr] at hs
          cases hs
          rw [readTerm_printTerm list h.1.1 hc.1 hul]
          simp only [ok_bind, readTerm_printTerm init h.1.2 hc.2.1 hui,
            readTerm_printTerm body h.2 hc.2.2 hub]
        · next hr => rw [hr] at hs; exact nomatch hs
  termination_by structural t

  theorem readTerms_printTerms {classes : Classes} {n : Nat} (ts : Terms)
      (h : Terms.scoped n ts = true) (hc : ts.covers classes = true)
      (hu : ts.unannotated = true) :
      readTerms classes n (printTerms n ts) = .ok ts :=
    match ts, h, hc, hu with
    | .nil, _, _, _ => by rw [printTerms, readTerms]
    | .cons t ts, h, hc, hu => by
      simp only [Terms.scoped, Bool.and_eq_true] at h
      rw [Terms.covers_cons, Bool.and_eq_true] at hc
      rw [Terms.unannotated_cons, Bool.and_eq_true] at hu
      simp only [printTerms, readTerms, readTerm_printTerm t h.1 hc.1 hu.1,
        readTerms_printTerms ts h.2 hc.2 hu.2, ok_bind]
  termination_by structural ts
end

mutual
  /-- **Term exactness**: what the term reader accepts, under any classes, prints back to
  exactly the expression it read. A class construction is accepted only when the printer prints
  the term it reads to as that construction, and a structural record only when it does not.
  Placed at R8 (`translation-simulation`) as a step of `read_exact`. -/
  theorem readTerm_exact {classes : Classes} {n : Nat} (x : Expr) {t : Term}
      (h : readTerm classes n x = .ok t) : printTerm n t = x := by
    rw [readTerm] at h
    split at h
    · next tag names values hcls =>
      have := Effect4.Codegen.Classes.readClass_size x tag names values hcls
      split at h
      · exact nomatch h
      · next fields _ =>
        obtain ⟨vs, hvs, h⟩ := bind_eq_ok.mp h
        split at h
        · next hct =>
          cases h
          rw [printTerm, hct]
          simp only [List.tail_cons, printTerms]
          rw [readTerms_exact values hvs]
          exact Effect4.Codegen.Classes.readClass_exact x tag names values hcls
        · exact nomatch h
    · split at h
      · next fields names values hr =>
        have := Effect4.Codegen.Record.readRecord_size x fields names values hr
        obtain ⟨vs, hvs, h⟩ := bind_eq_ok.mp h
        split at h
        · next hnone =>
          cases h
          rw [printTerm, Option.isNone_iff_eq_none.mp hnone]
          dsimp only
          rw [readTerms_exact values hvs]
          exact Effect4.Codegen.Record.readRecord_exact x fields names values hr
        · exact nomatch h
      · split at h
        · next optional name target hf =>
          have := Effect4.Codegen.Record.readField_size x optional name target hf
          obtain ⟨term, hterm, ht⟩ := map_eq_ok.mp h
          cases ht
          rw [printTerm, readTerm_exact target hterm]
          cases optional <;> exact Effect4.Codegen.Record.readField_exact x _ name target hf
        · split at h
          · next name target value hs =>
            have := Effect4.Codegen.Record.readSet_size x name target value hs
            simp only [bind_eq_ok] at h
            obtain ⟨targetTerm, htarget, valueTerm, hvalue, ht⟩ := h
            cases ht
            rw [printTerm, readTerm_exact target htarget, readTerm_exact value hvalue]
            exact Effect4.Codegen.Record.readSet_exact x name target value hs
          · split at h
            · next index target ht =>
              have := Effect4.Codegen.Tuple.readAt_size x index target ht
              obtain ⟨term, hterm, heq⟩ := map_eq_ok.mp h
              cases heq
              rw [printTerm, readTerm_exact target hterm]
              exact Effect4.Codegen.Tuple.readAt_exact x index target ht
            · split at h
              -- a fold: its three parts print back, the body two levels up, to the image
              -- without a type argument, which is the expression read
              · next list init body hl =>
                have := Effect4.Codegen.ListFold.read_size n x list init body hl
                simp only [bind_eq_ok] at h
                obtain ⟨l, hlist, i, hinit, b, hbody, ht⟩ := h
                cases ht
                rw [printTerm, Option.map_none, readTerm_exact list hlist,
                  readTerm_exact init hinit, readTerm_exact body hbody]
                exact Effect4.Codegen.ListFold.read_exact n x list init body hl
              · split at h
                · next s =>
                  split at h
                  · next i hi =>
                    cases h
                    obtain ⟨hs, _⟩ := Var.read_exact hi
                    exact congrArg Expr.ident hs.symm
                  · split at h
                    · next hs => cases h; exact congrArg Expr.ident hs.symm
                    · exact nomatch h
                · next k =>
                  split at h
                  · next hk =>
                    cases h
                    exact congrArg Expr.int (Int.toNat_of_nonneg hk)
                  · exact nomatch h
                · cases h; rfl
                · cases h; rfl
                ·
                  obtain ⟨terms, hterms, ht⟩ := map_eq_ok.mp h
                  cases ht
                  rw [printTerm, readTerms_exact _ hterms]
                · exact nomatch h
  termination_by sizeOf x
  decreasing_by all_goals subst_vars; all_goals simp_wf; all_goals omega

  theorem readTerms_exact {classes : Classes} {n : Nat} (xs : List Expr) {ts : Terms}
      (h : readTerms classes n xs = .ok ts) : printTerms n ts = xs := by
    cases hxs : xs with
    | nil =>
      rw [hxs] at h
      simp only [readTerms] at h; cases h; rfl
    | cons x rest =>
      rw [hxs] at h
      simp only [readTerms, bind_eq_ok] at h
      obtain ⟨t, ht, ts', hts', hts⟩ := h
      cases hts
      rw [printTerms, readTerm_exact x ht, readTerms_exact rest hts']
  termination_by sizeOf xs
  decreasing_by all_goals subst_vars; all_goals simp_wf; all_goals omega
end

theorem readLiteral_print (value : Lit) : readLiteral (printLit value) = .ok value := by
  unfold readLiteral
  have ht := readTerm_printTerm (classes := []) (n := 0) (.lit value) rfl
    (Term.covers_lit_nil value) rfl
  change readTerm [] 0 (printLit value) = .ok (.lit value) at ht
  rw [ht]
  rfl

theorem readLiteral_exact {x : Expr} {value : Lit} (h : readLiteral x = .ok value) :
    printLit value = x := by
  simp only [readLiteral, bind_eq_ok] at h
  obtain ⟨term, ht, h⟩ := h
  cases term with
  | var _ | app _ _ | record _ _ _ | field _ _ _ | recordSet _ _ _ | tupleAt _ _
  | fold _ _ _ _ => cases h
  | lit v =>
    cases h
    exact readTerm_exact x ht

/-! ## Causes, fork options, rows: the small round trips -/

section Rows

variable {classes : Classes}


theorem headOf_lit (h : Head) (s : String) (hs : h.spelling = s) : headOf s = some h :=
  hs ▸ headOf_spelling h

theorem readCause_printCause {n : Nat} (c : CauseTerm) (h : CauseTerm.scoped n c = true)
    (hc : c.covers classes = true) (hu : c.unannotated = true) :
    readCause classes n (printCause n c) = .ok c := by
  induction c with
  | fail e =>
    simp only [CauseTerm.scoped] at h
    rw [CauseTerm.covers_fail] at hc
    rw [CauseTerm.unannotated_fail] at hu
    rw [printCause]; unfold readCause; simp [headOf_lit .causeFail "Cause.fail" rfl, readTerm_printTerm e h hc hu]
  | die d =>
    simp only [CauseTerm.scoped] at h
    rw [CauseTerm.covers_die] at hc
    rw [CauseTerm.unannotated_die] at hu
    rw [printCause]; unfold readCause; simp [headOf_lit .causeDie "Cause.die" rfl, readTerm_printTerm d h hc hu]
  | interrupt who =>
    cases who with
    | none => rw [printCause]; unfold readCause; simp [headOf_lit .causeInterrupt "Cause.interrupt" rfl]
    | some w =>
      simp only [CauseTerm.scoped] at h
      rw [CauseTerm.covers_interrupt, Option.all_some] at hc
      rw [CauseTerm.unannotated_interrupt, Option.all_some] at hu
      rw [printCause]; unfold readCause; simp [headOf_lit .causeInterrupt "Cause.interrupt" rfl, readTerm_printTerm w h hc hu]
  | both l r ihl ihr =>
    simp only [CauseTerm.scoped, Bool.and_eq_true] at h
    rw [CauseTerm.covers_both, Bool.and_eq_true] at hc
    rw [CauseTerm.unannotated_both, Bool.and_eq_true] at hu
    rw [printCause]; unfold readCause; simp [headOf_lit .causeCombine "Cause.combine" rfl, ihl h.1 hc.1 hu.1, ihr h.2 hc.2 hu.2]

theorem readCause_exact {n : Nat} (x : Expr) {c : CauseTerm} (h : readCause classes n x = .ok c) :
    printCause n c = x := by
  induction x using readCause.induct generalizing c with
  | case1 s e hh =>
    unfold readCause at h; simp only [hh, map_eq_ok] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp [printCause, Head.spelling, readTerm_exact e ht, headOf_exact hh]
  | case2 s d hh =>
    unfold readCause at h; simp only [hh, map_eq_ok] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp [printCause, Head.spelling, readTerm_exact d ht, headOf_exact hh]
  | case3 s hh => unfold readCause at h; simp only [hh] at h; cases h; simp [printCause, Head.spelling, headOf_exact hh]
  | case4 s w hh =>
    unfold readCause at h; simp only [hh, map_eq_ok] at h
    obtain ⟨t, ht, rfl⟩ := h
    simp [printCause, Head.spelling, readTerm_exact w ht, headOf_exact hh]
  | case5 s l r hh ihl ihr =>
    unfold readCause at h; simp only [hh, bind_eq_ok] at h
    obtain ⟨a, ha, b, hb, hab⟩ := h
    cases hab
    simp [printCause, Head.spelling, ihl ha, ihr hb, headOf_exact hh]
  | case6 s args h1 h2 h3 h4 h5 => unfold readCause at h; split at h <;> simp_all
  | case7 t hne => unfold readCause at h; split at h <;> simp_all

theorem readForkOptions_print (o : Effect4.Supervision.ForkOptions) :
    readForkOptions o.daemon (printForkOptions o) = .ok o := by
  obtain ⟨s, d, m⟩ := o
  cases m <;> simp [printForkOptions, readForkOptions]

theorem readForkOptions_exact {d : Bool} {x : Expr} {o : Effect4.Supervision.ForkOptions}
    (h : readForkOptions d x = .ok o) : printForkOptions o = x ∧ o.daemon = d := by
  unfold readForkOptions at h
  split at h
  · split at h
    · rename_i hf
      split at h
      · cases h; simp [printForkOptions, hf]
      · cases h; simp [printForkOptions, hf]
      · split at h
        · cases h; rename_i hs; simp [printForkOptions, hf, hs]
        · cases h
      · cases h
    · cases h
  · cases h

theorem idents?_map (l : List String) : idents? (l.map Expr.ident) = some l := by
  induction l with
  | nil => rfl
  | cons s rest ih => simp [idents?, ih]

theorem idents?_exact {args : List Expr} {l : List String} (h : idents? args = some l) :
    args = l.map Expr.ident := by
  induction args generalizing l with
  | nil => simp [idents?] at h; subst h; rfl
  | cons x rest ih =>
    cases x <;> (unfold idents? at h; simp at h)
    obtain ⟨l', hl', rfl⟩ := h
    simp [ih hl']

theorem idents?_cons_none {e : Expr} {l : List Expr} (h : ∀ x, e ≠ Expr.ident x) :
    idents? (e :: l) = none := by
  cases e <;> first | exact absurd rfl (h _) | (unfold idents?; simp)

theorem idents?_printTerms {n : Nat} : ∀ ts : Terms, idents? (printTerms n ts) = ts.names?
  | .nil => rfl
  | .cons t rest => by
    cases t with
    | var i => simp only [printTerms, printTerm, idents?, Terms.names?, idents?_printTerms rest]
    | lit v => cases v <;>
        simp only [printTerms, printTerm, printLit, idents?, Terms.names?, idents?_printTerms rest]
    | app a args => rfl
    | record fields names values =>
      simp only [printTerms, printTerm, Terms.names?]
      split
      · rfl
      · simp only [Effect4.Codegen.Record.writeRecord]
        split <;> rfl
    | field mode target name => rfl
    | recordSet target name value => rfl
    | tupleAt target index => rfl
    | fold accTy list init body => rfl

theorem printTerm_ident {n : Nat} {t : Term} {x : String} (h : printTerm n t = .ident x) :
    (∃ i, t = .var i ∧ x = Var.name i) ∨ (t = .lit .unit ∧ x = "undefined") := by
  cases t with
  | var i => exact .inl ⟨i, rfl, (Expr.ident.inj h).symm⟩
  | lit v =>
    cases v with
    | unit => exact .inr ⟨rfl, (Expr.ident.inj h).symm⟩
    | nat _ | bool _ | str _ => exact nomatch h
  | app a args => exact nomatch h
  | record fields names values =>
    simp only [printTerm] at h
    split at h
    · exact nomatch h
    · simp only [Effect4.Codegen.Record.writeRecord] at h
      split at h <;> exact nomatch h
  | field mode target name => exact nomatch h
  | recordSet target name value => exact nomatch h
  | tupleAt target index => exact nomatch h
  | fold accTy list init body => exact nomatch h

theorem printTerm_eq_bool {n : Nat} (term : Term) (value : Bool) :
    printTerm n term = .bool value ↔ term = .lit (.bool value) := by
  cases term with
  | var _ => simp only [printTerm, reduceCtorEq]
  | app _ _ => simp only [printTerm, reduceCtorEq]
  | lit literal => cases literal <;>
      simp only [printTerm, printLit, Term.lit.injEq, Lit.bool.injEq, Expr.bool.injEq, reduceCtorEq]
  | record fields names values =>
    simp only [printTerm]
    split
    · simp only [Effect4.Codegen.Classes.writeClass, reduceCtorEq]
    · simp only [Effect4.Codegen.Record.writeRecord]
      split <;> simp only [reduceCtorEq]
  | field mode target name =>
    simp only [printTerm, Effect4.Codegen.Record.writeField, reduceCtorEq]
  | recordSet target name replacement =>
    simp only [printTerm, Effect4.Codegen.Record.writeSet, reduceCtorEq]
  | tupleAt target index =>
    simp only [printTerm, Effect4.Codegen.Tuple.writeAt, reduceCtorEq]
  | fold accTy list init body =>
    simp only [printTerm, Effect4.Codegen.ListFold.write, reduceCtorEq]

/-- An atom application that is no row reads as no row call, so the caller may read it as a
term. -/
theorem readRowCall_none {sig : Signature Op} {spell : String → List String → Option Op} {n : Nat}
    {atom : String} {args : Terms} (h : noRow spell atom args = true) :
    readRowCall classes sig spell n atom [] (printTerms n args) = none := by
  cases args with
  | nil =>
    simp only [noRow, Bool.and_true, Option.isNone_iff_eq_none] at h
    unfold readRowCall; rw [idents?_printTerms, h]; simp [printTerms]
  | cons t rest =>
    cases rest with
    | nil =>
      simp only [noRow, Bool.and_eq_true, Bool.and_true, Option.isNone_iff_eq_none] at h
      unfold readRowCall
      rw [idents?_printTerms (.cons t .nil), h.1]
      simp only [printTerms]
      rw [show idents? ([] : List Expr) = Terms.nil.names? from rfl, h.2]
    | cons u names =>
      simp only [noRow, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
      unfold readRowCall
      rw [idents?_printTerms (.cons t (.cons u names)), h.1]
      rw [printTerms.eq_2]
      dsimp only
      rw [idents?_printTerms (.cons u names), h.2.1]
      rw [printTerms.eq_2]
      dsimp only
      rw [idents?_printTerms names, h.2.2]

/-- A row whose type arguments parse has a readable head. -/
theorem rowHeadReadable_of_typeArgs {row : Row} {typeArgs : List TypeScript.TypeRef}
    (h : rowTypeArgs row = some typeArgs) : rowHeadReadable row = true := by
  simp only [rowHeadReadable, h, Option.isSome_some, Bool.or_true]

/-- A value row has a readable head: it prints none. -/
theorem rowHeadReadable_of_value {row : Row} (h : row.shape = .value) :
    rowHeadReadable row = true := by
  simp only [rowHeadReadable, h, decide_true, Bool.true_or]

/-- A method's argument row has a readable head only when the method's row does: the projection
keeps the type arguments and is never a value row. -/
theorem rowHeadReadable_of_method {row : Row} (h : rowHeadReadable (methodArgsRow row) = true) :
    rowHeadReadable row = true := by
  simp only [rowHeadReadable, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  rcases h with h | h
  · rcases methodArgsRow_shape row with hs | hs <;> rw [hs] at h <;> cases h
  · exact Or.inr h

/-- The face of an operation has the operation's row: a row does not depend on the binder term
(`LawfulSpelling.withTerm_row`). A step of the row lemmas below, which read a row's call back to
the face that `spell` answers. -/
theorem LawfulSpelling.face_row {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) (op : Op) : sig.rowOf (sig.face op) = sig.rowOf op :=
  hl.withTerm_row op _

/-- An operation that carries no binder term is its own face. A step of the row call's round
trip at a term-free row (`readRow_rowCall_print`, `Laws/Codegen/ReadPrint.lean`). -/
theorem LawfulSpelling.face_of_none {sig : Signature Op}
    {spell : String → List String → Option Op} (hl : LawfulSpelling sig spell) {op : Op}
    (h : sig.termOf op = none) : sig.face op = op :=
  hl.withTerm_none op _ h

theorem readRowCall_unit {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true)
    (hshape : (sig.rowOf op).shape = .call) (hreq : (sig.rowOf op).request = Ty.unit)
    {typeArgs : List TypeScript.TypeRef}
    (hta : rowTypeArgs (sig.rowOf op) = some typeArgs) :
    readRowCall classes sig spell n (sig.rowOf op).spelling typeArgs
        ((sig.rowOf op).trailing.map Expr.ident)
      = some (.ok (rowAnswer (sig.rowOf op) (sig.face op) (.lit .unit))) := by
  unfold readRowCall
  rw [idents?_map, Option.bind_some, hl.spell_row op hd (rowHeadReadable_of_typeArgs hta)]
  simp [hl.face_row, hshape, hreq, hta]

theorem readRowCall_request {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true) (r : Term)
    (hshape : (sig.rowOf op).shape = .call) (hreq : (sig.rowOf op).request ≠ Ty.unit)
    {typeArgs : List TypeScript.TypeRef}
    (hta : rowTypeArgs (sig.rowOf op) = some typeArgs) :
    readRowCall classes sig spell n (sig.rowOf op).spelling typeArgs
        (printTerm n r :: (sig.rowOf op).trailing.map Expr.ident)
      = some ((readTerm classes n (printTerm n r)).map
          (rowAnswer (sig.rowOf op) (sig.face op))) := by
  have key : ∀ x, (∀ op', x ∉ (sig.rowOf op').trailing) →
      spell (sig.rowOf op).spelling (x :: (sig.rowOf op).trailing) = none := by
    intro x hx
    cases hsp : spell (sig.rowOf op).spelling (x :: (sig.rowOf op).trailing) with
    | none => rfl
    | some op' =>
      exfalso
      obtain ⟨_, htr⟩ := hl.row_of_spell _ _ _ hsp
      exact hx op' (htr ▸ List.mem_cons_self)
  have hA : ((idents? (printTerm n r :: (sig.rowOf op).trailing.map Expr.ident)).bind
      (spell (sig.rowOf op).spelling)) = none := by
    cases he : printTerm n r with
    | ident name =>
      rcases printTerm_ident he with ⟨i, _, hn⟩ | ⟨_, hn⟩
      · subst name
        simp only [idents?, idents?_map, Option.map_some, Option.bind_some,
          key (Var.name i) (fun op' => hl.trailing_ne_name op' i)]
      · subst name
        simp only [idents?, idents?_map, Option.map_some, Option.bind_some,
          key "undefined" hl.trailing_ne_undefined]
    | _ => rfl
  unfold readRowCall
  rw [hA]
  dsimp only
  rw [idents?_map, Option.bind_some, hl.spell_row op hd (rowHeadReadable_of_typeArgs hta)]
  simp [hl.face_row, hshape, hreq, hta]

/-! ## `read_print`: what the printer prints of a readable program reads back to it -/

theorem readable_row_unit {row : Row} {n : Nat} {r : Term} (hshape : row.shape = .call)
    (hreq : row.request = Ty.unit) (h : requestReadable row n r = true) : r = .lit .unit := by
  simp only [requestReadable, hshape, hreq, if_true, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2

theorem readable_row_value {row : Row} {n : Nat} {r : Term} (hshape : row.shape = .value)
    (h : requestReadable row n r = true) : r = .lit .unit := by
  simp only [requestReadable, hshape, decide_eq_true_eq] at h; exact h

theorem readable_row_request {row : Row} {n : Nat} {r : Term} (hshape : row.shape = .call)
    (hreq : row.request ≠ Ty.unit) (h : requestReadable row n r = true) : r.scoped n = true := by
  simp only [requestReadable, hshape, hreq, if_false, Bool.and_eq_true] at h; exact h.2

/-- A printed term is an identifier only as a binder or as `undefined`, never as a trailing
name of any row. -/
theorem printTerm_ident_not_trailing {sig : Signature Op} {n : Nat}
    {spell : String → List String → Option Op} (hl : LawfulSpelling sig spell) (r : Term)
    (op : Op) (v : String) (h : printTerm n r = .ident v) : v ∉ (sig.rowOf op).trailing := by
  rcases printTerm_ident h with ⟨i, _, hv⟩ | ⟨_, hv⟩
  · subst v; exact hl.trailing_ne_name op i
  · subst v; exact hl.trailing_ne_undefined op

/-- The tuple reading of a row: two arguments that are not trailing names, then the row's
trailing names, read through `readTupleArgs`. -/
theorem readRowCall_tuple {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true) (x y : Expr)
    (hshape : (sig.rowOf op).shape = .tupleCall)
    (hx : ∀ op' v, x = .ident v → v ∉ (sig.rowOf op').trailing)
    (hy : ∀ op' v, y = .ident v → v ∉ (sig.rowOf op').trailing) {typeArgs : List TypeScript.TypeRef}
    (hta : rowTypeArgs (sig.rowOf op) = some typeArgs) :
    readRowCall classes sig spell n (sig.rowOf op).spelling typeArgs
        (x :: y :: (sig.rowOf op).trailing.map Expr.ident)
      = some ((readTupleArgs classes n x y).map (rowAnswer (sig.rowOf op) (sig.face op))) := by
  have key : ∀ (names : List String) (v : String), (∀ op', v ∉ (sig.rowOf op').trailing) →
      spell (sig.rowOf op).spelling (v :: names) = none := by
    intro names v hv
    cases hsp : spell (sig.rowOf op).spelling (v :: names) with
    | none => rfl
    | some op' =>
      exfalso
      obtain ⟨_, htr⟩ := hl.row_of_spell _ _ _ hsp
      exact hv op' (htr ▸ List.mem_cons_self)
  have hA : ((idents? (x :: y :: (sig.rowOf op).trailing.map Expr.ident)).bind
      (spell (sig.rowOf op).spelling)) = none := by
    cases x
    case ident v =>
      cases y
      case ident w =>
        simp only [idents?, idents?_map, Option.map_some, Option.bind_some]
        exact key _ v (fun op' => hx op' v rfl)
      all_goals simp [idents?]
    all_goals simp [idents?]
  have hB : ((idents? (y :: (sig.rowOf op).trailing.map Expr.ident)).bind
      (spell (sig.rowOf op).spelling)) = none := by
    cases y
    case ident w =>
      simp only [idents?, idents?_map, Option.map_some, Option.bind_some]
      exact key _ w (fun op' => hy op' w rfl)
    all_goals simp [idents?]
  unfold readRowCall
  rw [hA]
  dsimp only
  rw [hB]
  dsimp only
  rw [idents?_map, Option.bind_some, hl.spell_row op hd (rowHeadReadable_of_typeArgs hta)]
  simp [hl.face_row, hshape, hta]

/-- The tuple request round trip is shared by free calls and receiver methods. -/
theorem readRowCall_printTupleArgs {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true)
    (hshape : (sig.rowOf op).shape = .tupleCall) (r : Term)
    (h : tupleRequestReadable n r = true) (hc : r.covers classes = true)
    (hu : r.unannotated = true) {typeArgs : List TypeScript.TypeRef}
    (hta : rowTypeArgs (sig.rowOf op) = some typeArgs) :
    readRowCall classes sig spell n (sig.rowOf op).spelling typeArgs
      (printTupleArgs n r ++ (sig.rowOf op).trailing.map Expr.ident) =
      some (.ok (rowAnswer (sig.rowOf op) (sig.face op) r)) := by
  simp only [tupleRequestReadable] at h
  rcases hpa : pairArgs? r with _ | ⟨x, y⟩
  · simp only [hpa] at h
    cases r with
    | var i =>
      simp only at h
      simp only [printTupleArgs, hpa, printTerm, List.cons_append, List.nil_append]
      rw [readRowCall_tuple hl op hd _ _ hshape
        (fun _ _ hx => by cases hx) (fun _ _ hy => by cases hy) hta]
      have hv : readTerm classes n (.ident (Var.name i)) = .ok (.var i) :=
        readTerm_printTerm (.var i) h rfl rfl
      simp [readTupleArgs, savedVar?, hv]
    | lit value =>
      cases value with
      | unit =>
        simp only [printTupleArgs, hpa, printTerm, printLit, List.cons_append, List.nil_append]
        rw [readRowCall_tuple hl op hd _ _ hshape
          (fun _ _ hx => by cases hx) (fun _ _ hy => by cases hy) hta]
        have hv : readTerm classes n (.ident "undefined") = .ok (.lit .unit) :=
          readTerm_printTerm (.lit .unit) rfl rfl rfl
        simp [readTupleArgs, savedVar?, hv]
      | nat _ | bool _ | str _ => simp at h
    | app _ _ | record _ _ _ | field _ _ _ | recordSet _ _ _ | tupleAt _ _
    | fold _ _ _ _ => cases h
  · simp only [hpa, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    obtain ⟨⟨hx, hy⟩, hsv⟩ := h
    obtain rfl := pairArgs?_some hpa
    rw [Term.covers_app, Terms.covers_cons, Terms.covers_cons, Bool.and_eq_true,
      Bool.and_eq_true] at hc
    rw [Term.unannotated_app, Terms.unannotated_cons, Terms.unannotated_cons, Bool.and_eq_true,
      Bool.and_eq_true] at hu
    simp only [printTupleArgs, hpa, List.cons_append, List.nil_append]
    rw [readRowCall_tuple hl op hd _ _ hshape
      (fun op' v hv => printTerm_ident_not_trailing hl x op' v hv)
      (fun op' v hv => printTerm_ident_not_trailing hl y op' v hv) hta]
    simp [readTupleArgs, hsv, readTerm_printTerm x hx hc.1 hu.1,
      readTerm_printTerm y hy hc.2.1 hu.2.1]

/-- Method projection keeps the same row identities and name hygiene. -/
theorem methodLawful {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) : LawfulSpelling (methodSignature sig) spell where
  spell_row := fun op hd hh => hl.spell_row op hd (rowHeadReadable_of_method hh)
  row_of_spell := hl.row_of_spell
  value_trailing := by
    intro op hv
    have hs := methodArgsRow_shape (sig.rowOf op)
    change (methodArgsRow (sig.rowOf op)).shape = .value at hv
    rcases hs with hs | hs <;> simp [hs] at hv
  spelling_ne_name := hl.spelling_ne_name
  spelling_not_reserved := hl.spelling_not_reserved
  trailing_ne_name := hl.trailing_ne_name
  trailing_ne_undefined := hl.trailing_ne_undefined
  withTerm_row := fun op f => congrArg methodArgsRow (hl.withTerm_row op f)
  termOf_withTerm := hl.termOf_withTerm
  withTerm_termOf := hl.withTerm_termOf
  withTerm_withTerm := hl.withTerm_withTerm
  withTerm_none := hl.withTerm_none

theorem readRowCall_methodArgs {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true) (args : Term)
    (h : (if (methodArgsRow (sig.rowOf op)).shape = .tupleCall then tupleRequestReadable n args
      else if (methodArgsRow (sig.rowOf op)).request = Ty.unit then decide (args = .lit .unit)
      else args.scoped n) = true) (hc : args.covers classes = true)
    (hu : args.unannotated = true) {typeArgs : List TypeScript.TypeRef}
    (hta : rowTypeArgs (sig.rowOf op) = some typeArgs) :
    readRowCall classes (methodSignature sig) spell n (sig.rowOf op).spelling typeArgs
      (printMethodArgs n (sig.rowOf op) args) =
        some (.ok (rowAnswer (sig.rowOf op) (sig.face op) args)) := by
  have hm := methodLawful hl
  rcases methodArgsRow_shape (sig.rowOf op) with hs | hs
  · simp only [hs, reduceCtorEq, if_false] at h
    by_cases ht : (methodArgsRow (sig.rowOf op)).request = Ty.unit
    · simp only [ht, if_true, decide_eq_true_eq] at h
      subst args
      simp only [printMethodArgs, hs, reduceCtorEq, if_false, ht, if_true]
      have result := readRowCall_unit (classes := classes) (n := n) hm op hd hs ht hta
      dsimp +instances only [methodSignature, methodArgsRow, rowAnswer] at result ⊢
      exact result
    · simp only [ht, if_false] at h
      simp only [printMethodArgs, hs, reduceCtorEq, if_false, ht]
      have result := readRowCall_request (classes := classes) (n := n) hm op hd args hs ht hta
      rw [readTerm_printTerm args h hc hu] at result
      simp only [map_ok] at result
      dsimp +instances only [methodSignature, methodArgsRow, rowAnswer] at result ⊢
      exact result
  · simp only [hs, if_true] at h
    simp only [printMethodArgs, hs, if_true]
    have result :=
      readRowCall_printTupleArgs (classes := classes) (n := n) hm op hd hs args h hc hu hta
    dsimp +instances only [methodSignature, methodArgsRow, rowAnswer] at result ⊢
    exact result

theorem readRowMethod_print {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true)
    (receiver args : Term) (hs : (sig.rowOf op).shape = .method)
    (hr : receiver.scoped n = true)
    (ha : (if (methodArgsRow (sig.rowOf op)).shape = .tupleCall then tupleRequestReadable n args
      else if (methodArgsRow (sig.rowOf op)).request = Ty.unit then decide (args = .lit .unit)
      else args.scoped n) = true) (hcr : receiver.covers classes = true)
    (hca : args.covers classes = true) (hur : receiver.unannotated = true)
    (hua : args.unannotated = true) {typeArgs : List TypeScript.TypeRef}
    (hta : rowTypeArgs (sig.rowOf op) = some typeArgs) :
    readRowMethod classes sig spell n (printTerm n receiver) (sig.rowOf op).spelling typeArgs
      (printMethodArgs n (sig.rowOf op) args) =
      .ok (rowAnswer (sig.rowOf op) (sig.face op)
        (.app "pair" (.cons receiver (.cons args .nil)))) := by
  simp only [readRowMethod, readTerm_printTerm receiver hr hcr hur, ok_bind,
    readRowCall_methodArgs hl op hd args ha hca hua hta, Option.getD_some]
  simp only [rowAnswer, addReceiver, hl.face_row, hs, if_true]

/-- The signature at the faces: no operation carries a binder term, so a `perform` prints as its
row's call alone (`printPerform`). The face reader (`readPerformFace`) reads no function, so what
it reads prints back under this signature (`readPerformFace_exact`). -/
def Signature.atFaces (sig : Signature Op) : Signature Op :=
  { sig with termOf := fun _ => none }

/-- The printed form of a row answer at the faces is the row's printed call. -/
theorem print_rowAnswer {sig : Signature Op} {n : Nat} (op : Op) (r : Term) :
    print sig.atFaces n (rowAnswer (sig.rowOf op) op r) = printRow n (sig.rowOf op) r := by
  simp only [rowAnswer, print_perform]
  rfl

/-- The reader's two call arms agree on a row's printed head: with no declared type
arguments it is a plain `spelling(...)` call, and with them a `spelling<T…>(...)` call; both
route to `readRowCall` at the row's own type arguments (`E4-CHECK-CE-013`). -/
theorem readPerform_printRowHead {sig : Signature Op} {spell : String → List String → Option Op}
    {n : Nat} (op : Op) (args : List Expr) (answer : Except ReadRefusal (Eff Op))
    (hhead : headOf (sig.rowOf op).spelling = none)
    {typeArgs : List TypeScript.TypeRef} (hta : rowTypeArgs (sig.rowOf op) = some typeArgs)
    (hrow : readRowCall classes sig spell n (sig.rowOf op).spelling typeArgs args = some answer)
    {head : Expr} (hp : printRowHead (sig.rowOf op) = .ok head) :
    readPerformFace classes sig spell n (.call head args) = answer := by
  cases typeArgs with
  | nil =>
    simp only [printRowHead, hta, Except.ok.injEq] at hp
    subst head
    simp only [readPerformFace, hhead, hrow, Option.getD_some]
  | cons a rest =>
    simp only [printRowHead, hta, Except.ok.injEq] at hp
    subst head
    simp only [readPerformFace, hrow, Option.getD_some]

/-- A successfully printed readable row reads back to its row answer at the operation's face:
the row's call shows no binder term, so the face reader answers the operation that `spell`
names (`Signature.face`). -/
theorem read_printRow {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true) (r : Term)
    (h : requestReadable (sig.rowOf op) n r = true) (hc : r.covers classes = true)
    (hu : r.unannotated = true) {x : Expr} (hp : printRow n (sig.rowOf op) r = .ok x) :
    readPerformFace classes sig spell n x = .ok (rowAnswer (sig.rowOf op) (sig.face op) r) := by
  have hname : ∀ i, Var.name i ≠ (sig.rowOf op).spelling := fun i => (hl.spelling_ne_name op i).symm
  have hhead : headOf (sig.rowOf op).spelling = none := headOf_none (hl.spelling_not_reserved op)
  cases hshape : (sig.rowOf op).shape with
  | value =>
    have hr := readable_row_value hshape h
    subst r
    have htr := hl.value_trailing op hshape
    have hsp := hl.spell_row op hd (rowHeadReadable_of_value hshape)
    rw [htr] at hsp
    simp only [printRow, hshape, Except.ok.injEq] at hp
    subst x
    simp [readPerformFace, Var.read_none hname, hhead, readRowValue, hsp, hl.face_row, hshape]
  | call =>
    have htypes : (rowTypeArgs (sig.rowOf op)).isSome = true := by
      simp only [requestReadable, hshape, Bool.and_eq_true] at h
      exact h.1
    obtain ⟨typeArgs, hta⟩ := Option.isSome_iff_exists.mp htypes
    simp only [printRow, hshape, bind_eq_ok] at hp
    obtain ⟨head, hprint, hp⟩ := hp
    by_cases hreq : (sig.rowOf op).request = Ty.unit
    · have hr := readable_row_unit hshape hreq h
      subst r
      simp only [hreq, if_true, Except.ok.injEq] at hp
      subst x
      exact readPerform_printRowHead op _ _ hhead hta
        (readRowCall_unit hl op hd hshape hreq hta) hprint
    · simp only [hreq, if_false, Except.ok.injEq] at hp
      subst x
      rw [readPerform_printRowHead op _ _ hhead hta
        (readRowCall_request hl op hd r hshape hreq hta) hprint]
      simp [readTerm_printTerm r (readable_row_request hshape hreq h) hc hu]
  | tupleCall =>
    simp only [requestReadable, hshape, Bool.and_eq_true] at h
    obtain ⟨typeArgs, hta⟩ := Option.isSome_iff_exists.mp h.1
    simp only [printRow, hshape, bind_eq_ok] at hp
    obtain ⟨head, hprint, hp⟩ := hp
    simp only [Except.ok.injEq] at hp
    subst x
    exact readPerform_printRowHead op _ _ hhead hta
      (readRowCall_printTupleArgs hl op hd hshape r h.2 hc hu hta) hprint
  | method =>
    simp only [requestReadable, hshape, Bool.and_eq_true] at h
    obtain ⟨typeArgs, hta⟩ := Option.isSome_iff_exists.mp h.1
    have h := h.2
    cases hpair : pairArgs? r with
    | none => simp [hpair] at h
    | some parts =>
      obtain ⟨receiver, args⟩ := parts
      simp only [hpair, Bool.and_eq_true_iff] at h
      obtain ⟨hr, ha⟩ := h
      obtain rfl := pairArgs?_some hpair
      rw [Term.covers_app, Terms.covers_cons, Terms.covers_cons, Bool.and_eq_true,
        Bool.and_eq_true] at hc
      rw [Term.unannotated_app, Terms.unannotated_cons, Terms.unannotated_cons,
        Bool.and_eq_true, Bool.and_eq_true] at hu
      have hm :=
        readRowMethod_print hl op hd receiver args hshape hr ha hc.1 hc.2.1 hu.1 hu.2.1 hta
      cases typeArgs with
      | nil =>
        simp only [printRow, hshape, pairArgs?, ↓reduceIte, printMethod, hta,
          Except.ok.injEq] at hp
        subst x
        simp [readPerformFace, readMethod, hm]
      | cons t ts =>
        simp only [printRow, hshape, pairArgs?, ↓reduceIte, printMethod, hta,
          Except.ok.injEq] at hp
        subst x
        simp [readPerformFace, readMethod, hm]

/-! ## The function after a row call's arguments (the state plan's T5)

An operation's binder term prints as a function of the current value after the row call's
arguments (`printPerform`). These are the steps of the row call's round trip at a term row:
no argument a row prints is such a function, so a row's own call splits to nothing, and the
call with the function splits back to the call and the function's body. -/

/-- A call none of whose arguments is a function of the binder due at level `n` splits to
nothing. A step of `splitFunction_printRow`. -/
theorem splitFunction_call_none {n : Nat} (head : Expr) {args : List Expr}
    (h : ∀ e ∈ args, Effect4.Codegen.Binders.read n [0] e = none) :
    splitFunction n (.call head args) = none := by
  simp only [splitFunction]
  cases hlast : args.getLast? with
  | none => rfl
  | some last =>
    obtain ⟨front, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
    rw [Option.bind_some, h last (List.mem_append_right front List.mem_cons_self), Option.map_none]

/-- The same of a method call. -/
theorem splitFunction_method_none {n : Nat} (receiver : Expr) (name : String) {args : List Expr}
    (h : ∀ e ∈ args, Effect4.Codegen.Binders.read n [0] e = none) :
    splitFunction n (.method receiver name args) = none := by
  simp only [splitFunction]
  cases hlast : args.getLast? with
  | none => rfl
  | some last =>
    obtain ⟨front, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
    rw [Option.bind_some, h last (List.mem_append_right front List.mem_cons_self), Option.map_none]

/-- A trailing name is no function. -/
theorem binders_read_idents {n : Nat} (names : List String) :
    ∀ e ∈ names.map Expr.ident, Effect4.Codegen.Binders.read n [0] e = none := by
  intro e he
  obtain ⟨name, _, rfl⟩ := List.mem_map.mp he
  rfl

/-- Neither argument of a tuple-call row is a function: each is a term's image, or a component
read of a saved variable. -/
theorem binders_read_printTupleArgs {n m : Nat} (r : Term) :
    ∀ e ∈ printTupleArgs m r, Effect4.Codegen.Binders.read n [0] e = none := by
  intro e he
  unfold printTupleArgs at he
  split at he
  · next x y _ =>
    rcases List.mem_cons.mp he with rfl | he
    · exact binders_read_printTerm x
    · rcases List.mem_cons.mp he with rfl | he
      · exact binders_read_printTerm y
      · exact nomatch he
  · rcases List.mem_cons.mp he with rfl | he
    · rfl
    · rcases List.mem_cons.mp he with rfl | he
      · rfl
      · exact nomatch he

/-- No argument of a method row's call is a function. -/
theorem binders_read_printMethodArgs {n m : Nat} (row : Row) (args : Term) :
    ∀ e ∈ printMethodArgs m row args, Effect4.Codegen.Binders.read n [0] e = none := by
  intro e he
  unfold printMethodArgs at he
  split at he
  · rcases List.mem_append.mp he with he | he
    · exact binders_read_printTupleArgs args e he
    · exact binders_read_idents row.trailing e he
  · split at he
    · exact binders_read_idents row.trailing e he
    · rcases List.mem_cons.mp he with rfl | he
      · exact binders_read_printTerm args
      · exact binders_read_idents row.trailing e he

/-- **A row's own call carries no function**: what `printRow` prints splits to nothing, so the
reader takes it as a term-free row call. A step of `readPerform_printPerform`. -/
theorem splitFunction_printRow {n : Nat} {row : Row} {r : Term} {x : Expr}
    (h : printRow n row r = .ok x) : splitFunction n x = none := by
  cases hshape : row.shape with
  | value =>
    simp only [printRow, hshape, Except.ok.injEq] at h
    subst x
    rfl
  | call =>
    simp only [printRow, hshape, bind_eq_ok] at h
    obtain ⟨head, _, h⟩ := h
    split at h
    · cases h
      exact splitFunction_call_none head (binders_read_idents row.trailing)
    · cases h
      refine splitFunction_call_none head fun e he => ?_
      rcases List.mem_cons.mp he with rfl | he
      · exact binders_read_printTerm r
      · exact binders_read_idents row.trailing e he
  | tupleCall =>
    simp only [printRow, hshape, bind_eq_ok] at h
    obtain ⟨head, _, h⟩ := h
    cases h
    refine splitFunction_call_none head fun e he => ?_
    rcases List.mem_append.mp he with he | he
    · exact binders_read_printTupleArgs r e he
    · exact binders_read_idents row.trailing e he
  | method =>
    simp only [printRow, hshape] at h
    split at h <;>
      (unfold printMethod at h
       split at h
       · exact nomatch h
       · cases h
         exact splitFunction_method_none _ _ (binders_read_printMethodArgs row _)
       · cases h
         exact splitFunction_call_none _ (binders_read_printMethodArgs row _))

/-- **Retraction of the function split**: a row call with the function of a body after its
arguments splits back to the call and the body. A step of `readPerform_printPerform`. -/
theorem splitFunction_withFunction {n : Nat} {spelling : String} {call body x : Expr}
    (h : withFunction spelling (Effect4.Codegen.Binders.write n [0] body) call = .ok x) :
    splitFunction n x = some (call, body) := by
  unfold withFunction at h
  split at h
  · cases h
    simp only [splitFunction, List.getLast?_concat, Option.bind_some,
      Effect4.Codegen.Binders.read_write, Option.map_some, List.dropLast_concat]
  · cases h
    simp only [splitFunction, List.getLast?_concat, Option.bind_some,
      Effect4.Codegen.Binders.read_write, Option.map_some, List.dropLast_concat]
  · exact nomatch h

/-- A row that is no value row prints a call or a method call, which carries a function. A step
of `printPerform_ok` (`Laws/Codegen/PrintReadable.lean`). -/
theorem withFunction_printRow {n : Nat} {row : Row} {r : Term} {call : Expr}
    (h : printRow n row r = .ok call) (hshape : row.shape ≠ .value) (spelling : String)
    (fn : Expr) : ∃ x, withFunction spelling fn call = .ok x := by
  cases hs : row.shape with
  | value => exact absurd hs hshape
  | call =>
    simp only [printRow, hs, bind_eq_ok] at h
    obtain ⟨head, _, h⟩ := h
    split at h <;> (cases h; exact ⟨_, rfl⟩)
  | tupleCall =>
    simp only [printRow, hs, bind_eq_ok] at h
    obtain ⟨head, _, h⟩ := h
    cases h
    exact ⟨_, rfl⟩
  | method =>
    simp only [printRow, hs] at h
    split at h <;>
      (unfold printMethod at h
       split at h
       · exact nomatch h
       · cases h
         exact ⟨_, rfl⟩
       · cases h
         exact ⟨_, rfl⟩)

/-- **The row call of `perform` reads back from its printing** at a node of level `n`: a
readable request on a row in the signature's domain, and a binder term that reads back on that
row (`termReadable`: scoped one level up, covered, unannotated, on a call row). The row's call
reads to the operation's face (`read_printRow`), the function's body to the term
(`readTerm_printTerm`), and installing the term in the face gives the operation back
(`LawfulSpelling.withTerm_withTerm`, `withTerm_termOf`). A step of `read_print` (R8), the
row-call case of `readT_print` (`Laws/Codegen/ReadPrint.lean`). It states nothing of a term that
states an accumulator type, which is printed and not read, nor of any host run. -/
theorem readPerform_printPerform {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} {op : Op} {r : Term} (hd : sig.dom op = true)
    (hreq : requestReadable (sig.rowOf op) n r = true) (hc : r.covers classes = true)
    (hu : r.unannotated = true)
    (hterm : termReadable classes n (sig.rowOf op) ((sig.termOf op).map (·.term)) = true)
    {x : Expr} (hp : printPerform sig n op r = .ok x) :
    readPerform classes sig spell n x = .ok (.perform op r) := by
  unfold printPerform at hp
  cases hb : sig.termOf op with
  | none =>
    rw [hb] at hp
    unfold readPerform
    rw [splitFunction_printRow hp, read_printRow hl op hd r hreq hc hu hp]
    simp only [Except.bind, rowAnswer, termFree, hl.face_of_none hb, hb, Option.isNone_none,
      ↓reduceIte]
  | some b =>
    rw [hb] at hp
    cases hcall : printRow n (sig.rowOf op) r with
    | error why => rw [hcall] at hp; exact nomatch hp
    | ok call =>
      rw [hcall] at hp
      rw [hb, Option.map_some] at hterm
      simp only [termReadable, Bool.and_eq_true] at hterm
      obtain ⟨⟨⟨hscoped, hcovers⟩, hunannotated⟩, _⟩ := hterm
      have hsome : (sig.termOf (sig.face op)).isSome = true := by
        have h := hl.termOf_withTerm op (.lit .unit)
        rw [hb, Option.map_some] at h
        obtain ⟨b', hb', _⟩ := Option.map_eq_some_iff.mp h
        exact Option.isSome_iff_exists.mpr ⟨b', hb'⟩
      unfold readPerform
      rw [splitFunction_withFunction hp]
      simp only [read_printRow hl op hd r hreq hc hu hcall, ok_bind,
        readTerm_printTerm b.term hscoped hcovers hunannotated, rowAnswer, installTerm, hsome,
        ↓reduceIte]
      rw [Signature.face, hl.withTerm_withTerm, hl.withTerm_termOf op b hb]

/-- The tuple reading reconstructs its two arguments: a saved variable prints as its two
component reads, any other pair as the printed components. -/
theorem readTupleArgs_exact {n : Nat} {x y : Expr} {r : Term}
    (h : readTupleArgs classes n x y = .ok r) : printTupleArgs n r = [x, y] := by
  unfold readTupleArgs at h
  split at h
  · rename_i v hv
    obtain ⟨rfl, rfl⟩ := savedVar?_some hv
    have hp := readTerm_exact (.ident v) h
    have hpa : pairArgs? r = none := by
      rcases printTerm_ident hp with ⟨i, hr, _⟩ | ⟨hr, _⟩
      · subst r; rfl
      · subst r; rfl
    simp [printTupleArgs, hpa, hp]
  · simp only [bind_eq_ok] at h
    obtain ⟨a, ha, b, hb, he⟩ := h
    cases he
    simp [printTupleArgs, pairArgs?, readTerm_exact x ha, readTerm_exact y hb]

section ReadExact

/-- Closes an arm of a wildcard case of the reader: the arm's own negated-pattern hypothesis
is contradictory, or the arm is a refusal. -/
scoped macro "close_arm" h:ident : tactic => `(tactic| first
  | (exfalso; subst_vars; solve_by_elim [rfl])
  | cases $h:ident
  | (split at $h:ident <;> first | (exfalso; subst_vars; solve_by_elim [rfl]) | cases $h:ident))

/-- The call reader recovers the method's row identity and exactly its argument syntax. -/
theorem readRowCall_method_parts {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} {s : String} {ta : List TypeScript.TypeRef} {args : List Expr}
    {e : Eff Op}
    (h : readRowCall classes (methodSignature sig) spell n s ta args = some (.ok e)) :
    ∃ op r, e = rowAnswer (sig.rowOf op) op r ∧ (sig.rowOf op).spelling = s ∧
      rowTypeArgs (sig.rowOf op) = some ta ∧ printMethodArgs n (sig.rowOf op) r = args := by
  unfold readRowCall at h
  split at h
  · rename_i op hA
    simp only [Option.some.injEq] at h
    split at h
    · rename_i hc
      dsimp only [methodSignature] at hc
      cases h
      obtain ⟨names, hn, hsp⟩ := Option.bind_eq_some_iff.mp hA
      obtain ⟨hs, htr⟩ := hl.row_of_spell _ _ _ hsp
      refine ⟨op, .lit .unit, rfl, hs, hc.2.2, ?_⟩
      rw [idents?_exact hn]
      simp only [printMethodArgs, hc.1, reduceCtorEq, if_false, hc.2.1, if_true, htr]
    · cases h
  · split at h
    · split at h
      · simp only [Option.some.injEq] at h
        split at h
        · rename_i hc
          dsimp only [methodSignature] at hc
          obtain ⟨r, hr, rfl⟩ := map_eq_ok.mp h
          obtain ⟨names, hn, hsp⟩ :=
            Option.bind_eq_some_iff.mp ‹(idents? _).bind (spell s) = some _›
          obtain ⟨hs, htr⟩ := hl.row_of_spell _ _ _ hsp
          refine ⟨_, r, rfl, hs, hc.2.2, ?_⟩
          rw [idents?_exact hn]
          simp only [printMethodArgs, hc.1, reduceCtorEq, if_false, hc.2.1, htr,
            readTerm_exact _ hr]
        · cases h
      · split at h
        · split at h
          · simp only [Option.some.injEq] at h
            split at h
            · rename_i hc
              dsimp only [methodSignature] at hc
              obtain ⟨r, hr, rfl⟩ := map_eq_ok.mp h
              obtain ⟨names, hn, hsp⟩ :=
                Option.bind_eq_some_iff.mp ‹(idents? _).bind (spell s) = some _›
              obtain ⟨hs, htr⟩ := hl.row_of_spell _ _ _ hsp
              refine ⟨_, r, rfl, hs, hc.2, ?_⟩
              rw [idents?_exact hn]
              simp only [printMethodArgs, hc.1, if_true, htr, readTupleArgs_exact hr,
                List.cons_append, List.nil_append]
            · cases h
          · cases h
        · cases h
    · cases h

theorem addReceiver_rowAnswer (sig : Signature Op) (receiver : Term) (op : Op) (args : Term) :
    addReceiver sig receiver (rowAnswer (sig.rowOf op) op args) =
      if (sig.rowOf op).shape = .method then
        .ok (rowAnswer (sig.rowOf op) op (.app "pair" (.cons receiver (.cons args .nil))))
      else .error (.shape "method row") := by
  unfold rowAnswer
  split <;> simp [addReceiver, rowAnswer, *]

theorem readRowMethod_exact {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} {receiver : Expr} {s : String}
    {ta : List TypeScript.TypeRef} {args : List Expr} {e : Eff Op}
    (h : readRowMethod classes sig spell n receiver s ta args = .ok e) :
    print sig.atFaces n e = .ok (match ta with
      | [] => .method receiver s args
      | ts => .call (.generic (.member receiver s) ts) args) := by
  unfold readRowMethod at h
  obtain ⟨recv, hr, h⟩ := bind_eq_ok.mp h
  obtain ⟨body, hb, h⟩ := bind_eq_ok.mp h
  cases hc : readRowCall classes (methodSignature sig) spell n s ta args with
  | none => simp [hc] at hb
  | some answer =>
    simp only [hc, Option.getD_some] at hb
    rw [hb] at hc
    obtain ⟨op, request, rfl, hs, ht, ha⟩ := readRowCall_method_parts hl hc
    rw [addReceiver_rowAnswer] at h
    split at h
    · rename_i hshape
      cases h
      simp [print_rowAnswer, printRow, hshape, pairArgs?, printMethod,
        hs, ht, ha, readTerm_exact _ hr]
      cases ta <;> rfl
    · cases h

theorem readMethod_exact {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} {x : Expr} {e : Eff Op}
    (h : readMethod classes sig spell n x = .ok e) : print sig.atFaces n e = .ok x := by
  unfold readMethod at h
  split at h
  · exact readRowMethod_exact hl h
  · exact readRowMethod_exact hl h
  · cases h

/-- What a row call reads from: `spelling(args)`, or `spelling<T…>(args)` when the row declares
type arguments. -/
def rowCallImage (s : String) (ta : List TypeScript.TypeRef) (args : List Expr) : Expr :=
  match ta with
  | [] => .call (.ident s) args
  | ta => .call (.generic (.ident s) ta) args

/-- The three readings of a row call, each printed back. One script closes them all: the row
the spelling names, its shape and type arguments from the reading's own test, the trailing names
from `idents?_exact`, and the request from its reader's exactness. -/
theorem readRowCall_exact {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} {s : String} {ta : List TypeScript.TypeRef}
    {args : List Expr} {e : Eff Op} (h : readRowCall classes sig spell n s ta args = some (.ok e)) :
    print sig.atFaces n e = .ok (rowCallImage s ta args) := by
  unfold readRowCall at h
  split at h
  · rename_i op hA
    simp only [Option.some.injEq] at h
    split at h
    · rename_i hc
      cases h
      obtain ⟨names, hnames, hsp⟩ := Option.bind_eq_some_iff.mp hA
      obtain ⟨hs, htr⟩ := hl.row_of_spell _ _ _ hsp
      rw [print_rowAnswer, idents?_exact hnames]
      cases ta <;> simp [rowCallImage, printRow, printRowHead, hc.1, hc.2.1, hc.2.2, hs, htr]
    · cases h
  · split at h
    · split at h
      · simp only [Option.some.injEq] at h
        split at h
        · rename_i hc
          simp only [map_eq_ok] at h
          obtain ⟨r, hr, he⟩ := h
          subst he
          obtain ⟨names, hnames, hsp⟩ :=
            Option.bind_eq_some_iff.mp ‹(idents? _).bind (spell s) = some _›
          obtain ⟨hs, htr⟩ := hl.row_of_spell _ _ _ hsp
          rw [print_rowAnswer, idents?_exact hnames]
          cases ta <;>
            simp [rowCallImage, printRow, printRowHead, hc.1, hc.2.1, hc.2.2, hs, htr,
              readTerm_exact _ hr]
        · cases h
      · split at h
        · split at h
          · simp only [Option.some.injEq] at h
            split at h
            · rename_i hshape
              simp only [map_eq_ok] at h
              obtain ⟨r, hr, he⟩ := h
              subst he
              obtain ⟨names, hnames, hsp⟩ :=
                Option.bind_eq_some_iff.mp ‹(idents? _).bind (spell s) = some _›
              obtain ⟨hs, htr⟩ := hl.row_of_spell _ _ _ hsp
              rw [print_rowAnswer, idents?_exact hnames]
              cases ta <;>
                simp [rowCallImage, printRow, printRowHead, hshape.1, hshape.2, hs, htr,
                  readTupleArgs_exact hr]
            · cases h
          · cases h
        · cases h
    · cases h

/-- A bare identifier read as a value row prints back. -/
theorem readRowValue_exact {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} {s : String} {e : Eff Op}
    (h : readRowValue sig spell s = .ok e) : print sig.atFaces n e = .ok (.ident s) := by
  unfold readRowValue at h
  split at h
  · rename_i op hsp
    split at h
    · rename_i hshape
      cases h
      obtain ⟨hs, _⟩ := hl.row_of_spell _ _ _ hsp
      rw [print_rowAnswer]
      simp [printRow, hshape, hs]
    · cases h
  · cases h

/-- The row call at the faces' level: what `readPerformFace` accepts prints back to the tree it
read, every operation at its own form. -/
theorem readPerformFace_exact {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} {x : Expr} {e : Eff Op}
    (h : readPerformFace classes sig spell n x = .ok e) : print sig.atFaces n e = .ok x := by
  unfold readPerformFace at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h
      · exact readRowValue_exact hl h
  · split at h <;> cases h
  · cases h
  · cases h
  · split at h
    · split at h <;> cases h
    · rename_i s args _ _
      cases hrow : readRowCall classes sig spell n s [] args with
      | none => rw [hrow] at h; cases h
      | some answer =>
        rw [hrow] at h
        simp only [Option.getD_some] at h
        subst h
        exact readRowCall_exact hl hrow
  · rename_i s ta tas args
    cases hrow : readRowCall classes sig spell n s (ta :: tas) args with
    | none => rw [hrow] at h; cases h
    | some answer =>
      rw [hrow] at h
      simp only [Option.getD_some] at h
      subst h
      exact readRowCall_exact hl hrow
  · exact readMethod_exact hl h

/-- **Exactness of the function split**: what `splitFunction` splits is the row call it answers
with the function back in its last place (`withFunction`). A step of `readPerform_exact`. -/
theorem withFunction_of_splitFunction {n : Nat} {x call body : Expr} (spelling : String)
    (h : splitFunction n x = some (call, body)) :
    withFunction spelling (Effect4.Codegen.Binders.write n [0] body) call = .ok x := by
  unfold splitFunction at h
  split at h
  · next head args =>
    obtain ⟨last, hlast, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨body', hbody, h⟩ := Option.map_eq_some_iff.mp h
    cases h
    obtain ⟨front, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
    rw [Effect4.Codegen.Binders.read_exact n [0] last body hbody, List.dropLast_concat]
    rfl
  · next receiver name args =>
    obtain ⟨last, hlast, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨body', hbody, h⟩ := Option.map_eq_some_iff.mp h
    cases h
    obtain ⟨front, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
    rw [Effect4.Codegen.Binders.read_exact n [0] last body hbody, List.dropLast_concat]
    rfl
  · exact nomatch h

/-- The row call of `perform`: what `readPerform` accepts prints back to the tree it read. The
face it reads prints as the row's call (`readPerformFace_exact`). Where a function follows the
call's arguments, its body is the term the reader installed (`readTerm_exact`), the printer
prints that term as the same function (`Binders.read_exact`) after the same call, since the row
does not depend on the term (`LawfulSpelling.withTerm_row`). Where none follows, the operation
carries no term, and the printer prints the row's call alone. A step of `read_exact` (R8). -/
theorem readPerform_exact {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} {x : Expr} {e : Eff Op}
    (h : readPerform classes sig spell n x = .ok e) : print sig n e = .ok x := by
  unfold readPerform at h
  split at h
  · next call body hsplit =>
    obtain ⟨face, hface, h⟩ := bind_eq_ok.mp h
    obtain ⟨f, hf, h⟩ := bind_eq_ok.mp h
    have hx := readPerformFace_exact hl hface
    cases face with
    | perform op r =>
      have hrow : printRow n (sig.rowOf op) r = .ok call := hx
      simp only [installTerm] at h
      split at h
      · next hsome =>
        cases h
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsome
        have hterm := hl.termOf_withTerm op f
        rw [hb, Option.map_some] at hterm
        obtain ⟨b', hb', hbt⟩ := Option.map_eq_some_iff.mp hterm
        rw [print_perform, printPerform, hb']
        dsimp only
        rw [hl.withTerm_row, hrow, hbt, readTerm_exact body hf]
        exact withFunction_of_splitFunction _ hsplit
      · exact nomatch h
    | _ => exact nomatch h
  · next hsplit =>
    cases hface : readPerformFace classes sig spell n x with
    | error why => rw [hface] at h; exact nomatch h
    | ok face =>
      rw [hface] at h
      have hx := readPerformFace_exact hl hface
      cases face with
      | perform op r =>
        have hrow : printRow n (sig.rowOf op) r = .ok x := hx
        simp only [Except.bind, termFree] at h
        split at h
        · next hnone =>
          cases h
          rw [print_perform, printPerform, Option.isNone_iff_eq_none.mp hnone]
          exact hrow
        · exact nomatch h
      | _ => exact nomatch h

end ReadExact

end Rows

theorem name_notin (l : List String) (h : ∀ s ∈ l, s.toByteArray.data.toList.head? ≠ some 97)
    (i : Nat) : Var.name i ∉ l := fun hm => Var.name_ne (h _ hm) i rfl

/-- No external operation is a built-in representative: every representative is a built-in row,
whose kind is not a host row's. -/
theorem NativeOp.external_not_mem_spelled (i : Nat) : NativeOp.external i ∉ NativeOp.spelled := by
  intro h
  have hall : NativeOp.spelled.all (fun op => decide (NativeOp.kind op ≠ .program)) = true := by
    decide
  exact of_decide_eq_true (List.all_eq_true.mp hall _ h) rfl

/-- A built-in operation keeps its own row whatever the supplied table. -/
theorem nativeRowOf_builtin (table : RowTable) (op : NativeOp) (h : ∀ i, op ≠ .external i) :
    nativeRowOf table op = op.row := by
  cases op with
  | external i => exact absurd rfl (h i)
  | _ => rfl

theorem nativeRowOf_external (table : RowTable) (i : Nat) (hi : i < table.length) :
    nativeRowOf table (.external i) = table[i] := by
  simp [nativeRowOf, List.getElem?_eq_getElem hi]

/-- Every native row's names are hygienic: the spelling and the trailing names are fixed by the
operation's key, never by a type argument or a binder term it carries. A term row has no
trailing name: the faces print its term as a function. -/
theorem NativeOp.row_hygiene (op : NativeOp) :
    (op.row.shape = .value → op.row.trailing = []) ∧ rowNamesSafe op.row = true := by
  cases op with
  | refUpdateWith f | refGetAndUpdateWith f | refUpdateAndGetWith f | refUpdateSomeWith f
  | refGetAndUpdateSomeWith f | refUpdateSomeAndGetWith f | refModifyWith f
  | refModifySomeWith f => exact ⟨fun hs => (by cases hs), rfl⟩
  | scopeMake s => cases s <;> decide
  | deferredMakeOf value error => exact ⟨fun hs => (by cases hs), rfl⟩
  | external i =>
    exact (by decide : (NativeOp.externalPlaceholder.shape = .value →
      NativeOp.externalPlaceholder.trailing = []) ∧ rowNamesSafe NativeOp.externalPlaceholder = true)
  | _ => decide

theorem lawfulTable_member (table : RowTable) (h : LawfulTable table = true)
    (row : Row) (hr : row ∈ table) :
    rowKey row ∉ builtinKeys ∧
    (row.shape = .value → row.trailing = []) ∧ rowNamesSafe row = true := by
  simp only [LawfulTable, Table.lawful, Bool.and_eq_true] at h
  refine ⟨?_, ?_, List.all_eq_true.mp h.2 row hr⟩
  · have hc := List.all_eq_true.mp h.1.1.2 row hr
    simpa [Row.key] using hc
  · have hv := List.all_eq_true.mp h.1.2 row hr
    intro hs
    simpa [hs] using hv

theorem nativeRow_hygiene (table : RowTable) (h : LawfulTable table = true) (op : NativeOp) :
    ((nativeRowOf table op).shape = .value → (nativeRowOf table op).trailing = []) ∧
      rowNamesSafe (nativeRowOf table op) = true := by
  cases op with
  | external i =>
    by_cases hi : i < table.length
    · rw [nativeRowOf_external table i hi]
      exact (lawfulTable_member table h _ (List.getElem_mem hi)).2
    · simp only [nativeRowOf, List.getElem?_eq_none (Nat.le_of_not_gt hi), Option.getD_none]
      decide
  | _ =>
    simp only [nativeRowOf]
    exact NativeOp.row_hygiene _

theorem nativeLawful (table : RowTable := []) (h : LawfulTable table = true := by decide) :
    LawfulSpelling (nativeSignature table) (nativeSpell table) where
  spell_row := by
    intro op hd hh
    cases op with
    -- a term row: its key names the row alone, and the spelling reads its face back
    | refUpdateWith f | refGetAndUpdateWith f | refUpdateAndGetWith f | refUpdateSomeWith f
    | refGetAndUpdateSomeWith f | refUpdateSomeAndGetWith f | refModifyWith f
    | refModifySomeWith f => rfl
    | external i =>
      have hi : i < table.length := of_decide_eq_true hd
      change nativeSpell table (nativeRowOf table (.external i)).spelling
        (nativeRowOf table (.external i)).trailing = some (.external i)
      rw [nativeRowOf_external table i hi]
      have hn : (table.map rowKey).Nodup := by
        simp only [LawfulTable, Table.lawful, Bool.and_eq_true, decide_eq_true_eq] at h
        exact h.1.1.1
      have hc := (lawfulTable_member table h _ (List.getElem_mem hi)).1
      have hb := builtinLookup_none (rowKey table[i]) hc
      have hf := rowIndex_roundTrip table hn i hi
      dsimp +instances only [rowKey] at hb hf
      unfold nativeSpell rowKey
      rw [hb, hf]
      rfl
    | scopeMake s => cases s <;> rfl
    | deferredMakeOf value error =>
      -- only the instance whose type arguments the faces spell reads back
      by_cases hve : value = .nat ∧ error = .nat
      · obtain ⟨rfl, rfl⟩ := hve
        rfl
      · have hargs : NativeOp.deferredTypeArgs value error = [""] := if_neg hve
        change (decide (RowShape.call = .value) ||
          ((NativeOp.deferredTypeArgs value error).mapM
            Effect4.Codegen.Types.parseLegacy).isSome) = true at hh
        rw [hargs] at hh
        exact absurd hh (by decide)
    | _ => rfl
  row_of_spell := by
    intro s names op hs
    unfold nativeSpell at hs
    split at hs
    · rename_i found hfound
      have heq : found = op := Option.some.inj hs
      subst op
      have hm := List.mem_of_find?_eq_some hfound
      have hk := List.find?_some
        (p := fun op : NativeOp => decide (rowKey op.row = (s, names))) hfound
      change (nativeRowOf table found).spelling = s ∧ (nativeRowOf table found).trailing = names
      rw [nativeRowOf_builtin table found
        (fun i he => NativeOp.external_not_mem_spelled i (he ▸ hm))]
      exact Prod.mk.inj (of_decide_eq_true hk)
    · obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hs
      obtain ⟨hlt, hk⟩ := rowIndex_exact table (s, names) i hi
      change (nativeRowOf table (.external i)).spelling = s ∧
        (nativeRowOf table (.external i)).trailing = names
      rw [nativeRowOf_external table i hlt]
      exact Prod.mk.inj hk
  value_trailing := fun op => (nativeRow_hygiene table h op).1
  spelling_ne_name := by
    intro op i
    have hn := (nativeRow_hygiene table h op).2
    simp only [rowNamesSafe, Bool.and_eq_true] at hn
    have hn := hn.1
    exact (Var.name_ne (by simpa [firstByte, nativeSignature, Program.Row.normalizeTypes] using hn.1.1) i).symm
  spelling_not_reserved := by
    intro op
    have hn := (nativeRow_hygiene table h op).2
    simp only [rowNamesSafe, Bool.and_eq_true] at hn
    have hn := hn.1
    simpa [nativeSignature, Program.Row.normalizeTypes] using hn.1.2
  trailing_ne_name := by
    intro op i
    have hn := (nativeRow_hygiene table h op).2
    simp only [rowNamesSafe, Bool.and_eq_true] at hn
    have hn := hn.1
    apply name_notin
    intro name hm
    have ht := List.all_eq_true.mp hn.2 name hm
    simpa only [firstByte, nativeSignature, Program.Row.normalizeTypes, bne_iff_ne,
      ne_eq, Bool.not_eq_true] using (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ht).1).1
  trailing_ne_undefined := by
    intro op hm
    have hn := (nativeRow_hygiene table h op).2
    simp only [rowNamesSafe, Bool.and_eq_true] at hn
    have hn := hn.1
    have ht := List.all_eq_true.mp hn.2 "undefined" hm
    simp at ht
  -- a row does not depend on its operation's term, and replacing the term is an exact update
  withTerm_row := by
    intro op f
    cases op <;> rfl
  termOf_withTerm := by
    intro op f
    cases op <;> rfl
  withTerm_termOf := by
    intro op b hb
    cases hbinder : op.binder? with
    | none =>
      change op.binder?.map (fun b => (⟨b.2, b.1.param, b.1.result⟩ : BinderTerm)) = some b at hb
      rw [hbinder] at hb
      exact nomatch hb
    | some st =>
      obtain ⟨shape, t⟩ := st
      change op.binder?.map (fun b => (⟨b.2, b.1.param, b.1.result⟩ : BinderTerm)) = some b at hb
      rw [hbinder] at hb
      cases hb
      exact NativeOp.withTerm_binder? hbinder
  withTerm_withTerm := fun op f g => NativeOp.withTerm_withTerm op f g
  withTerm_none := by
    intro op f hnone
    change op.binder?.map (fun b => (⟨b.2, b.1.param, b.1.result⟩ : BinderTerm)) = none at hnone
    exact NativeOp.withTerm_of_none (Option.map_eq_none_iff.mp hnone) f

end Effect4.Program
