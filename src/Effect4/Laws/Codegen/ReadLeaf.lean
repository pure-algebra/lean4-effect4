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

/-- The inversion of a bind that succeeds: `Laws.Auto.bind_eq_ok` (`Laws/Auto/Inversion.lean`),
whose statement it is. -/
theorem bind_eq_ok {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β} :
    (m >>= f) = .ok b ↔ ∃ a, m = .ok a ∧ f a = .ok b :=
  Effect4.Laws.Auto.bind_eq_ok

/-- The inversion of a map that succeeds: `Laws.Auto.map_eq_ok`, whose statement it is. -/
theorem map_eq_ok {ε α β : Type} {m : Except ε α} {f : α → β} {b : β} :
    m.map f = .ok b ↔ ∃ a, m = .ok a ∧ f a = b :=
  Effect4.Laws.Auto.map_eq_ok

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

theorem rowArgs?_map (l : List RowArg) : rowArgs? (l.map RowArg.print) = some l := by
  induction l with
  | nil => rfl
  | cons a rest ih => cases a <;> simp only [List.map_cons, RowArg.print, rowArgs?, ih, Option.map_some]

theorem rowArgs?_exact {args : List Expr} {l : List RowArg} (h : rowArgs? args = some l) :
    args = l.map RowArg.print := by
  induction args generalizing l with
  | nil =>
    simp only [rowArgs?, Option.some.injEq] at h
    subst h
    rfl
  | cons x rest ih =>
    cases x
    case ident s =>
      simp only [rowArgs?, Option.map_eq_some_iff] at h
      obtain ⟨l', hl', rfl⟩ := h
      simp only [List.map_cons, RowArg.print, ih hl']
    case str v =>
      simp only [rowArgs?, Option.map_eq_some_iff] at h
      obtain ⟨l', hl', rfl⟩ := h
      simp only [List.map_cons, RowArg.print, ih hl']
    all_goals simp only [rowArgs?, reduceCtorEq] at h

theorem rowArgs?_printTerms {n : Nat} : ∀ ts : Terms, rowArgs? (printTerms n ts) = ts.rowArgs?
  | .nil => rfl
  | .cons t rest => by
    cases t with
    | var i => simp only [printTerms, printTerm, rowArgs?, Terms.rowArgs?, rowArgs?_printTerms rest]
    | lit v => cases v <;>
        simp only [printTerms, printTerm, printLit, rowArgs?, Terms.rowArgs?,
          rowArgs?_printTerms rest]
    | app a args => rfl
    | record fields names values =>
      simp only [printTerms, printTerm, Terms.rowArgs?]
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

/-- A printed term is a string literal only as the literal itself. -/
theorem printTerm_eq_str {n : Nat} (term : Term) (value : String) :
    printTerm n term = .str value ↔ term = .lit (.str value) := by
  cases term with
  | var _ => simp only [printTerm, reduceCtorEq]
  | app _ _ => simp only [printTerm, reduceCtorEq]
  | lit literal => cases literal <;>
      simp only [printTerm, printLit, Term.lit.injEq, Lit.str.injEq, Expr.str.injEq, reduceCtorEq]
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
theorem readRowCall_none {sig : Signature Op} {spell : String → List RowArg → Option Op} {n : Nat}
    {atom : String} {args : Terms} (h : noRow spell atom args = true) :
    readRowCall classes sig spell n atom [] (printTerms n args) = none := by
  cases args with
  | nil =>
    simp only [noRow, Bool.and_true, Option.isNone_iff_eq_none] at h
    unfold readRowCall; rw [rowArgs?_printTerms, h]; simp [printTerms]
  | cons t rest =>
    cases rest with
    | nil =>
      simp only [noRow, Bool.and_eq_true, Bool.and_true, Option.isNone_iff_eq_none] at h
      unfold readRowCall
      rw [rowArgs?_printTerms (.cons t .nil), h.1]
      simp only [printTerms]
      rw [show rowArgs? ([] : List Expr) = Terms.nil.rowArgs? from rfl, h.2]
    | cons u names =>
      simp only [noRow, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
      unfold readRowCall
      rw [rowArgs?_printTerms (.cons t (.cons u names)), h.1]
      rw [printTerms.eq_2]
      dsimp only
      rw [rowArgs?_printTerms (.cons u names), h.2.1]
      rw [printTerms.eq_2]
      dsimp only
      rw [rowArgs?_printTerms names, h.2.2]

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

/-! ### The columns a printed call shows, at the face (the state plan's T5, part B)

The face of an operation drops its binder term and its type arguments (`Signature.face`). The
row does not depend on the term (`LawfulSpelling.withTerm_row`). It does depend on the type
arguments, in its answer and error columns, so the face has the operation's row only in the
columns that a printed call shows (`Row.callColumns`): the spelling, the shape, the trailing
names, the request and the declared type arguments. The row lemmas below read a row's call back
to the face that `spell` answers, and they consult these columns alone. The restored operation,
not the face, owns the answer and error columns. -/

theorem Row.callColumns_spelling {a b : Row} (h : a.callColumns = b.callColumns) :
    a.spelling = b.spelling := congrArg (·.1) h

theorem Row.callColumns_shape {a b : Row} (h : a.callColumns = b.callColumns) :
    a.shape = b.shape := congrArg (·.2.1) h

theorem Row.callColumns_trailing {a b : Row} (h : a.callColumns = b.callColumns) :
    a.trailing = b.trailing := congrArg (·.2.2.1) h

theorem Row.callColumns_request {a b : Row} (h : a.callColumns = b.callColumns) :
    a.request = b.request := congrArg (·.2.2.2.1) h

theorem Row.callColumns_typeArgs {a b : Row} (h : a.callColumns = b.callColumns) :
    a.typeArgs = b.typeArgs := congrArg (·.2.2.2.2) h

/-- Rows with the same call columns declare the same type arguments. -/
theorem Row.callColumns_rowTypeArgs {a b : Row} (h : a.callColumns = b.callColumns) :
    rowTypeArgs a = rowTypeArgs b := by
  simp only [rowTypeArgs, Row.callColumns_typeArgs h]

/-- The method projection reads the request alone, so it keeps equal call columns equal. A step
of `LawfulTypeArgs.method`. -/
theorem methodArgsRow_callColumns {a b : Row} (h : a.callColumns = b.callColumns) :
    (methodArgsRow a).callColumns = (methodArgsRow b).callColumns := by
  simp only [Row.callColumns, methodArgsRow, Row.callColumns_spelling h,
    Row.callColumns_trailing h, Row.callColumns_request h, Row.callColumns_typeArgs h]

/-- The row answer does not read its row: it is a `perform` of the operation. The row lemmas
state their answers at the operation's own row, and the reader builds them at the face's. -/
theorem rowAnswer_eq (row : Row) (op : Op) : rowAnswer row op = Eff.perform op := rfl

/-- **The face keeps the columns a printed call shows.** The term does not move the row
(`withTerm_row`), and the type arguments do not move these columns (`LawfulTypeArgs.call`). A
step of the row lemmas below. -/
theorem LawfulKeys.face_callColumns {sig : Signature Op}
    {spell : String → List RowArg → Option Op} (hl : LawfulKeys sig spell) (op : Op) :
    (sig.rowOf (sig.face op)).callColumns = (sig.rowOf op).callColumns :=
  (hl.typeArgs.call _ _).trans (congrArg Row.callColumns (hl.withTerm_row op _))

theorem LawfulKeys.face_shape {sig : Signature Op} {spell : String → List RowArg → Option Op}
    (hl : LawfulKeys sig spell) (op : Op) :
    (sig.rowOf (sig.face op)).shape = (sig.rowOf op).shape :=
  Row.callColumns_shape (hl.face_callColumns op)

theorem LawfulKeys.face_request {sig : Signature Op}
    {spell : String → List RowArg → Option Op} (hl : LawfulKeys sig spell) (op : Op) :
    (sig.rowOf (sig.face op)).request = (sig.rowOf op).request :=
  Row.callColumns_request (hl.face_callColumns op)

theorem LawfulKeys.face_rowTypeArgs {sig : Signature Op}
    {spell : String → List RowArg → Option Op} (hl : LawfulKeys sig spell) (op : Op) :
    rowTypeArgs (sig.rowOf (sig.face op)) = rowTypeArgs (sig.rowOf op) :=
  Row.callColumns_rowTypeArgs (hl.face_callColumns op)

/-- An operation that carries no type argument is fixed by a replacement of its type arguments.
It follows from the update laws: the arity is fixed, so the replaced operation carries none, and
replacing by its own type arguments twice is replacing once. -/
theorem LawfulTypeArgs.withTypeArgs_none {sig : Signature Op} (h : LawfulTypeArgs sig) {op : Op}
    (hnone : sig.typeArgsOf op = []) (tys : List Ty) : sig.withTypeArgs op tys = op := by
  have hnil : sig.typeArgsOf (sig.withTypeArgs op tys) = [] :=
    List.eq_nil_of_length_eq_zero (by simp only [h.length_typeArgsOf, hnone, List.length_nil])
  have h1 := h.withTypeArgs_typeArgsOf (sig.withTypeArgs op tys)
  rw [hnil, h.withTypeArgs_withTypeArgs] at h1
  have h2 := h.withTypeArgs_typeArgsOf op
  rw [hnone] at h2
  exact h1.symm.trans h2

/-- The face carries as many type arguments as the operation: the arity is the row key's. -/
theorem LawfulKeys.length_typeArgsOf_face {sig : Signature Op}
    {spell : String → List RowArg → Option Op} (hl : LawfulKeys sig spell) (op : Op) :
    (sig.typeArgsOf (sig.face op)).length = (sig.typeArgsOf op).length := by
  rw [Signature.face, hl.typeArgs.length_typeArgsOf, hl.typeArgs.typeArgsOf_withTerm]

/-- **The face with the operation's type arguments restored** is the operation at its term's
face. The two updates commute, and replacing the type arguments by the operation's own is the
operation. A step of `readCall_printCall`. -/
theorem LawfulKeys.withTypeArgs_face {sig : Signature Op}
    {spell : String → List RowArg → Option Op} (hl : LawfulKeys sig spell) (op : Op) :
    sig.withTypeArgs (sig.face op) (sig.typeArgsOf op) = sig.withTerm op (.lit .unit) := by
  rw [Signature.face, hl.typeArgs.withTypeArgs_withTypeArgs, hl.typeArgs.withTypeArgs_withTerm,
    hl.typeArgs.withTypeArgs_typeArgsOf]

/-- An operation that carries no binder term and no type argument is its own face. -/
theorem LawfulKeys.face_of_none {sig : Signature Op}
    {spell : String → List RowArg → Option Op} (hl : LawfulKeys sig spell) {op : Op}
    (h : sig.termOf op = none) (hnone : sig.typeArgsOf op = []) : sig.face op = op := by
  rw [Signature.face, hl.withTerm_none op _ h, hl.typeArgs.withTypeArgs_none hnone]

/-- No key of the spelling `s` begins with a string literal. A reading of a printed request
under `s` needs it: the request may print as a string literal, which reads like the first
trailing argument of such a key. `LawfulSpelling.literal_alone` gives it under the spelling of
every operation of the domain that prints its request (`LawfulSpelling.literalClear`). -/
def LiteralClear (spell : String → List RowArg → Option Op) (s : String) : Prop :=
  ∀ v names, spell s (.str v :: names) = none

theorem LawfulSpelling.literalClear {sig : Signature Op}
    {spell : String → List RowArg → Option Op} (hl : LawfulSpelling sig spell) {op : Op}
    (hd : sig.dom op = true) (hp : (sig.rowOf op).printsRequest = true) :
    LiteralClear spell (sig.rowOf op).spelling :=
  fun v names => hl.literal_alone op v names hd hp

theorem readRowCall_unit {sig : Signature Op} {spell : String → List RowArg → Option Op}
    (hl : LawfulKeys sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true)
    (hshape : (sig.rowOf op).shape = .call) (hreq : (sig.rowOf op).request = Ty.unit)
    {typeArgs : List TypeScript.TypeRef}
    (hta : rowTypeArgs (sig.rowOf op) = some typeArgs) :
    readRowCall classes sig spell n (sig.rowOf op).spelling typeArgs
        ((sig.rowOf op).trailing.map RowArg.print)
      = some (.ok (rowAnswer (sig.rowOf op) (sig.face op) (.lit .unit))) := by
  unfold readRowCall
  rw [rowArgs?_map, Option.bind_some, hl.spell_row op hd (rowHeadReadable_of_typeArgs hta)]
  simp [rowAnswer_eq, hl.face_shape, hl.face_request, hl.face_rowTypeArgs, hshape, hreq, hta]

/-- A printed term is an identifier only as a binder or as `undefined`, never as a trailing
name of any row. -/
theorem printTerm_ident_not_trailing {sig : Signature Op} {n : Nat}
    {spell : String → List RowArg → Option Op} (hl : LawfulKeys sig spell) (r : Term)
    (op : Op) (v : String) (h : printTerm n r = .ident v) :
    RowArg.name v ∉ (sig.rowOf op).trailing := by
  rcases printTerm_ident h with ⟨i, _, hv⟩ | ⟨_, hv⟩
  · subst v; exact hl.trailing_ne_name op i
  · subst v; exact hl.trailing_ne_undefined op

/-- **A printed request begins no key of its row's spelling.** As an identifier it is no row's
trailing name; as a string literal it begins no key of that spelling (`LiteralClear`); as
anything else it is no trailing argument at all. -/
theorem spell_request_none {sig : Signature Op} {spell : String → List RowArg → Option Op}
    (hl : LawfulKeys sig spell) {op : Op} (hstr : LiteralClear spell (sig.rowOf op).spelling) {x : Expr}
    (hx : ∀ op' v, x = .ident v → RowArg.name v ∉ (sig.rowOf op').trailing) (rest : List Expr) :
    (rowArgs? (x :: rest)).bind (spell (sig.rowOf op).spelling) = none := by
  cases hr : rowArgs? (x :: rest) with
  | none => rfl
  | some l =>
    rw [Option.bind_some]
    cases hsp : spell (sig.rowOf op).spelling l with
    | none => rfl
    | some op' =>
      exfalso
      obtain ⟨_, htr⟩ := hl.row_of_spell _ _ _ hsp
      cases x
      case ident v =>
        simp only [rowArgs?, Option.map_eq_some_iff] at hr
        obtain ⟨l', _, rfl⟩ := hr
        exact hx op' v rfl (htr ▸ List.mem_cons_self)
      case str v =>
        simp only [rowArgs?, Option.map_eq_some_iff] at hr
        obtain ⟨l', _, rfl⟩ := hr
        rw [hstr v l'] at hsp
        cases hsp
      all_goals simp only [rowArgs?, reduceCtorEq] at hr

theorem readRowCall_request {sig : Signature Op} {spell : String → List RowArg → Option Op}
    (hl : LawfulKeys sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true) (r : Term)
    (hshape : (sig.rowOf op).shape = .call) (hreq : (sig.rowOf op).request ≠ Ty.unit)
    (hstr : LiteralClear spell (sig.rowOf op).spelling) {typeArgs : List TypeScript.TypeRef}
    (hta : rowTypeArgs (sig.rowOf op) = some typeArgs) :
    readRowCall classes sig spell n (sig.rowOf op).spelling typeArgs
        (printTerm n r :: (sig.rowOf op).trailing.map RowArg.print)
      = some ((readTerm classes n (printTerm n r)).map
          (rowAnswer (sig.rowOf op) (sig.face op))) := by
  unfold readRowCall
  rw [spell_request_none hl hstr (fun op' v hv => printTerm_ident_not_trailing hl r op' v hv)]
  dsimp only
  rw [rowArgs?_map, Option.bind_some, hl.spell_row op hd (rowHeadReadable_of_typeArgs hta)]
  simp [rowAnswer_eq, hl.face_shape, hl.face_request, hl.face_rowTypeArgs, hshape, hreq, hta]

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

/-- The tuple reading of a row: two arguments that are not trailing names, then the row's
trailing arguments, read through `readTupleArgs`. -/
theorem readRowCall_tuple {sig : Signature Op} {spell : String → List RowArg → Option Op}
    (hl : LawfulKeys sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true) (x y : Expr)
    (hshape : (sig.rowOf op).shape = .tupleCall) (hstr : LiteralClear spell (sig.rowOf op).spelling)
    (hx : ∀ op' v, x = .ident v → RowArg.name v ∉ (sig.rowOf op').trailing)
    (hy : ∀ op' v, y = .ident v → RowArg.name v ∉ (sig.rowOf op').trailing)
    {typeArgs : List TypeScript.TypeRef} (hta : rowTypeArgs (sig.rowOf op) = some typeArgs) :
    readRowCall classes sig spell n (sig.rowOf op).spelling typeArgs
        (x :: y :: (sig.rowOf op).trailing.map RowArg.print)
      = some ((readTupleArgs classes n x y).map (rowAnswer (sig.rowOf op) (sig.face op))) := by
  unfold readRowCall
  rw [spell_request_none hl hstr hx]
  dsimp only
  rw [spell_request_none hl hstr hy]
  dsimp only
  rw [rowArgs?_map, Option.bind_some, hl.spell_row op hd (rowHeadReadable_of_typeArgs hta)]
  simp [rowAnswer_eq, hl.face_shape, hl.face_rowTypeArgs, hshape, hta]

/-- The tuple request round trip is shared by free calls and receiver methods. -/
theorem readRowCall_printTupleArgs {sig : Signature Op} {spell : String → List RowArg → Option Op}
    (hl : LawfulKeys sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true)
    (hshape : (sig.rowOf op).shape = .tupleCall) (hstr : LiteralClear spell (sig.rowOf op).spelling) (r : Term)
    (h : tupleRequestReadable n r = true) (hc : r.covers classes = true)
    (hu : r.unannotated = true) {typeArgs : List TypeScript.TypeRef}
    (hta : rowTypeArgs (sig.rowOf op) = some typeArgs) :
    readRowCall classes sig spell n (sig.rowOf op).spelling typeArgs
      (printTupleArgs n r ++ (sig.rowOf op).trailing.map RowArg.print) =
      some (.ok (rowAnswer (sig.rowOf op) (sig.face op) r)) := by
  simp only [tupleRequestReadable] at h
  rcases hpa : pairArgs? r with _ | ⟨x, y⟩
  · simp only [hpa] at h
    cases r with
    | var i =>
      simp only at h
      simp only [printTupleArgs, hpa, printTerm, List.cons_append, List.nil_append]
      rw [readRowCall_tuple hl op hd _ _ hshape hstr
        (fun _ _ hx => by cases hx) (fun _ _ hy => by cases hy) hta]
      have hv : readTerm classes n (.ident (Var.name i)) = .ok (.var i) :=
        readTerm_printTerm (.var i) h rfl rfl
      simp [readTupleArgs, savedVar?, hv]
    | lit value =>
      cases value with
      | unit =>
        simp only [printTupleArgs, hpa, printTerm, printLit, List.cons_append, List.nil_append]
        rw [readRowCall_tuple hl op hd _ _ hshape hstr
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
    rw [readRowCall_tuple hl op hd _ _ hshape hstr
      (fun op' v hv => printTerm_ident_not_trailing hl x op' v hv)
      (fun op' v hv => printTerm_ident_not_trailing hl y op' v hv) hta]
    simp [readTupleArgs, hsv, readTerm_printTerm x hx hc.1 hu.1,
      readTerm_printTerm y hy hc.2.1 hu.2.1]

/-- The method projection keeps the laws of an operation's type arguments. It changes the row by
its request alone, so equal call columns stay equal, and it changes no other hook. -/
theorem LawfulTypeArgs.method {sig : Signature Op} (h : LawfulTypeArgs sig) :
    LawfulTypeArgs (methodSignature sig) where
  call := fun op tys => methodArgsRow_callColumns (h.call op tys)
  typeArgsOf_withTypeArgs := h.typeArgsOf_withTypeArgs
  length_typeArgsOf := h.length_typeArgsOf
  withTypeArgs_typeArgsOf := h.withTypeArgs_typeArgsOf
  withTypeArgs_withTypeArgs := h.withTypeArgs_withTypeArgs
  withTypeArgs_withTerm := h.withTypeArgs_withTerm
  termOf_withTypeArgs := h.termOf_withTypeArgs
  typeArgsOf_withTerm := h.typeArgsOf_withTerm

/-- Method projection keeps the same row identities and name hygiene. It does not keep
`LawfulSpelling.literal_alone`: there every non-method row prints a request. -/
theorem methodLawful {sig : Signature Op} {spell : String → List RowArg → Option Op}
    (hl : LawfulKeys sig spell) : LawfulKeys (methodSignature sig) spell where
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
  typeArgs := hl.typeArgs.method

theorem readRowCall_methodArgs {sig : Signature Op} {spell : String → List RowArg → Option Op}
    (hl : LawfulKeys sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true)
    (hstr : LiteralClear spell (sig.rowOf op).spelling) (args : Term)
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
      have result :=
        readRowCall_request (classes := classes) (n := n) hm op hd args hs ht hstr hta
      rw [readTerm_printTerm args h hc hu] at result
      simp only [map_ok] at result
      dsimp +instances only [methodSignature, methodArgsRow, rowAnswer] at result ⊢
      exact result
  · simp only [hs, if_true] at h
    simp only [printMethodArgs, hs, if_true]
    have result :=
      readRowCall_printTupleArgs (classes := classes) (n := n) hm op hd hs hstr args h hc hu
        hta
    dsimp +instances only [methodSignature, methodArgsRow, rowAnswer] at result ⊢
    exact result

theorem readRowMethod_print {sig : Signature Op} {spell : String → List RowArg → Option Op}
    (hl : LawfulKeys sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true)
    (hstr : LiteralClear spell (sig.rowOf op).spelling) (receiver args : Term) (hs : (sig.rowOf op).shape = .method)
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
    readRowCall_methodArgs hl op hd hstr args ha hca hua hta, Option.getD_some]
  simp only [rowAnswer, addReceiver, hl.face_shape, hs, if_true]

/-- The signature at the faces: no operation carries a binder term or a type argument, so a
`perform` prints as its row's call alone (`printPerform`). The face reader (`readPerformFace`)
reads no function and no type argument of an operation, so what it reads prints back under this
signature (`readPerformFace_exact`). -/
def Signature.atFaces (sig : Signature Op) : Signature Op :=
  { sig with termOf := fun _ => none, typeArgsOf := fun _ => [] }

/-- The printed form of a row answer at the faces is the row's printed call. -/
theorem print_rowAnswer {sig : Signature Op} {n : Nat} (op : Op) (r : Term) :
    print sig.atFaces n (rowAnswer (sig.rowOf op) op r) = printRow n (sig.rowOf op) r := by
  simp only [rowAnswer, print_perform]
  rfl

/-- The reader's two call arms agree on a row's printed head: with no declared type
arguments it is a plain `spelling(...)` call, and with them a `spelling<T…>(...)` call; both
route to `readRowCall` at the row's own type arguments (`E4-CHECK-CE-013`). -/
theorem readPerform_printRowHead {sig : Signature Op} {spell : String → List RowArg → Option Op}
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
theorem read_printRow {sig : Signature Op} {spell : String → List RowArg → Option Op}
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
    simp [readPerformFace, Var.read_none hname, hhead, readRowValue, hsp, rowAnswer_eq,
      hl.face_shape, hshape]
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
        (readRowCall_unit hl.toLawfulKeys op hd hshape hreq hta) hprint
    · simp only [hreq, if_false, Except.ok.injEq] at hp
      subst x
      have hstr := hl.literalClear hd (by simp only [Row.printsRequest, hshape, hreq,
        decide_false, Bool.not_false])
      rw [readPerform_printRowHead op _ _ hhead hta
        (readRowCall_request hl.toLawfulKeys op hd r hshape hreq hstr hta) hprint]
      simp [readTerm_printTerm r (readable_row_request hshape hreq h) hc hu]
  | tupleCall =>
    simp only [requestReadable, hshape, Bool.and_eq_true] at h
    obtain ⟨typeArgs, hta⟩ := Option.isSome_iff_exists.mp h.1
    simp only [printRow, hshape, bind_eq_ok] at hp
    obtain ⟨head, hprint, hp⟩ := hp
    simp only [Except.ok.injEq] at hp
    subst x
    have hstr := hl.literalClear hd (by simp only [Row.printsRequest, hshape])
    exact readPerform_printRowHead op _ _ hhead hta
      (readRowCall_printTupleArgs hl.toLawfulKeys op hd hshape hstr r h.2 hc hu hta) hprint
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
      have hstr := hl.literalClear hd (by simp only [Row.printsRequest, hshape])
      have hm := readRowMethod_print hl.toLawfulKeys op hd hstr receiver args hshape hr ha hc.1
        hc.2.1 hu.1 hu.2.1 hta
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
  simp only [splitFunction, lastArgument?]
  cases hlast : args.getLast? with
  | none => rfl
  | some last =>
    obtain ⟨front, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
    rw [Option.map_some, Option.bind_some,
      h last (List.mem_append_right front List.mem_cons_self), Option.map_none]

/-- The same of a method call. -/
theorem splitFunction_method_none {n : Nat} (receiver : Expr) (name : String) {args : List Expr}
    (h : ∀ e ∈ args, Effect4.Codegen.Binders.read n [0] e = none) :
    splitFunction n (.method receiver name args) = none := by
  simp only [splitFunction, lastArgument?]
  cases hlast : args.getLast? with
  | none => rfl
  | some last =>
    obtain ⟨front, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
    rw [Option.map_some, Option.bind_some,
      h last (List.mem_append_right front List.mem_cons_self), Option.map_none]

/-- A trailing argument is no function: a name or a string literal. -/
theorem binders_read_rowArgs {n : Nat} (args : List RowArg) :
    ∀ e ∈ args.map RowArg.print, Effect4.Codegen.Binders.read n [0] e = none := by
  intro e he
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp he
  cases a <;> rfl

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
    · exact binders_read_rowArgs row.trailing e he
  · split at he
    · exact binders_read_rowArgs row.trailing e he
    · rcases List.mem_cons.mp he with rfl | he
      · exact binders_read_printTerm args
      · exact binders_read_rowArgs row.trailing e he

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
      exact splitFunction_call_none head (binders_read_rowArgs row.trailing)
    · cases h
      refine splitFunction_call_none head fun e he => ?_
      rcases List.mem_cons.mp he with rfl | he
      · exact binders_read_printTerm r
      · exact binders_read_rowArgs row.trailing e he
  | tupleCall =>
    simp only [printRow, hshape, bind_eq_ok] at h
    obtain ⟨head, _, h⟩ := h
    cases h
    refine splitFunction_call_none head fun e he => ?_
    rcases List.mem_append.mp he with he | he
    · exact binders_read_printTupleArgs r e he
    · exact binders_read_rowArgs row.trailing e he
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
    simp only [splitFunction, lastArgument?, List.getLast?_concat, Option.bind_some,
      Effect4.Codegen.Binders.read_write, Option.map_some, List.dropLast_concat]
  · cases h
    simp only [splitFunction, lastArgument?, List.getLast?_concat, Option.bind_some,
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

/-! ## The type arguments on a row call's head (the state plan's T5, part B)

An operation's type arguments print on the head of its row's call (`printCall`,
`withHeadTypes`), each as the type printer prints it. The reader takes them off the head
(`splitHeadTypes`), reads the call at its face, reads each type through the checked type reader
and installs the list (`readCall`, `installTypeArgs`). These are the steps of that round trip.

Placement: concept `translation-simulation`, serving R4's first open part and R8. The consumers
are `readPerform_printPerform` and `readPerform_exact` below, the row-call steps of `read_print`
and `read_exact`. Reach: any lawful signature; the retraction asks for readable type arguments
(`typeArgsReadable`, over `Classes.ReadableTy`), and exactness asks for nothing. They do not
establish target typing or a host run, and they say nothing of a type outside `ReadableTy`. -/

/-- **Retraction of the head split**: a row call with type arguments on its head splits back to
the call and the arguments. A step of `readCall_printCall`. -/
theorem splitHeadTypes_withHeadTypes {spelling : String} {target : TypeScript.TypeRef}
    {targets : List TypeScript.TypeRef} {call x : Expr}
    (h : withHeadTypes spelling (target :: targets) call = .ok x) :
    splitHeadTypes x = some (call, target :: targets) := by
  unfold withHeadTypes at h
  split at h
  · cases h
    rfl
  · cases h
    rfl
  · exact nomatch h

/-- **Exactness of the head split**: what `splitHeadTypes` splits is the call it answers with
the type arguments back on its head (`withHeadTypes`). A step of `readCall_exact`. -/
theorem withHeadTypes_of_splitHeadTypes {x call : Expr} {targets : List TypeScript.TypeRef}
    (spelling : String) (h : splitHeadTypes x = some (call, targets)) :
    withHeadTypes spelling targets call = .ok x := by
  unfold splitHeadTypes at h
  split at h
  · cases h
    rfl
  · cases h
    rfl
  · exact nomatch h

/-- The split's type arguments are never the empty list. -/
theorem splitHeadTypes_ne_nil {x call : Expr} {targets : List TypeScript.TypeRef}
    (h : splitHeadTypes x = some (call, targets)) : targets ≠ [] := by
  unfold splitHeadTypes at h
  split at h
  · cases h
    exact List.cons_ne_nil _ _
  · cases h
    exact List.cons_ne_nil _ _
  · exact nomatch h

/-- Type arguments on the head leave the argument list as it is: a call that carries no
function still carries none. A step of `splitFunction_printCall`. -/
theorem splitFunction_withHeadTypes {n : Nat} {spelling : String}
    {targets : List TypeScript.TypeRef} {call x : Expr}
    (h : withHeadTypes spelling targets call = .ok x) (hnone : splitFunction n call = none) :
    splitFunction n x = none := by
  unfold withHeadTypes at h
  split at h
  · next s args =>
    cases h
    cases hlast : args.getLast? with
    | none => simp only [splitFunction, lastArgument?, hlast, Option.map_none, Option.bind_none]
    | some last =>
      simp only [splitFunction, lastArgument?, hlast, Option.map_some, Option.bind_some,
        Option.map_eq_none_iff] at hnone ⊢
      exact hnone
  · next receiver name args =>
    cases h
    cases hlast : args.getLast? with
    | none => simp only [splitFunction, lastArgument?, hlast, Option.map_none, Option.bind_none]
    | some last =>
      simp only [splitFunction, lastArgument?, hlast, Option.map_some, Option.bind_some,
        Option.map_eq_none_iff] at hnone ⊢
      exact hnone
  · exact nomatch h

/-- **A row's call with its type arguments carries no function**: what `printCall` prints
splits to nothing, so the reader takes it as a term-free row call. A step of
`readPerform_printPerform`. -/
theorem splitFunction_printCall {sig : Signature Op} {n : Nat} {op : Op} {r : Term} {x : Expr}
    (h : printCall sig n op r = .ok x) : splitFunction n x = none := by
  unfold printCall at h
  split at h
  · exact splitFunction_printRow h
  · split at h
    · cases hcall : printRow n (sig.rowOf op) r with
      | error why =>
        rw [hcall] at h
        exact nomatch h
      | ok call =>
        rw [hcall] at h
        exact splitFunction_withHeadTypes h (splitFunction_printRow hcall)
    · exact nomatch h

/-- **A row call's declared type arguments are determined.** Where a call reads at one list of
type arguments, the same call is refused at every other list, by its spelling: the spelling and
the trailing names select the arm, the type arguments do not, and each arm checks them. So the
two readings of `readCall` do not overlap: a call that reads with its head's type arguments as
the row's own does not read without them. A step of `readPerformFace_bare_error`. -/
theorem readRowCall_typeArgs_ne {sig : Signature Op} {spell : String → List RowArg → Option Op}
    {n : Nat} {s : String} {ta ta' : List TypeScript.TypeRef} {args : List Expr} {e : Eff Op}
    (h : readRowCall classes sig spell n s ta args = some (.ok e)) (hne : ta' ≠ ta) :
    readRowCall classes sig spell n s ta' args = some (.error (.arity s)) := by
  unfold readRowCall at h ⊢
  -- each split of the reading at `ta` selects the same arm of the reading at `ta'`
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · next hc => rw [if_neg fun hc' => hne (Option.some.inj (hc'.2.2.symm.trans hc.2.2))]
    · exact nomatch h
  · split at h
    · split at h
      · simp only [Option.some.injEq] at h
        split at h
        · next hc => rw [if_neg fun hc' => hne (Option.some.inj (hc'.2.2.symm.trans hc.2.2))]
        · exact nomatch h
      · split at h
        · split at h
          · simp only [Option.some.injEq] at h
            split at h
            · next hc => rw [if_neg fun hc' => hne (Option.some.inj (hc'.2.symm.trans hc.2))]
            · exact nomatch h
          · exact nomatch h
        · exact nomatch h
    · exact nomatch h

/-- **The two readings of a typed head do not overlap.** A call whose head's type arguments the
face reader reads as the row's own declared ones does not read at its face without them. So
`readCall` reads a row's declared type arguments through its second reading. A step of
`readCall_printCall` at an operation that carries no type argument. -/
theorem readPerformFace_bare_error {sig : Signature Op}
    {spell : String → List RowArg → Option Op} {n : Nat} {x bare : Expr}
    {targets : List TypeScript.TypeRef} {e : Eff Op}
    (hsplit : splitHeadTypes x = some (bare, targets))
    (h : readPerformFace classes sig spell n x = .ok e) :
    ∃ why, readPerformFace classes sig spell n bare = .error why := by
  unfold splitHeadTypes at hsplit
  split at hsplit
  · next s target rest args =>
    cases hsplit
    simp only [readPerformFace] at h
    cases hrow : readRowCall classes sig spell n s (target :: rest) args with
    | none =>
      rw [hrow] at h
      cases h
    | some answer =>
      rw [hrow, Option.getD_some] at h
      subst h
      have hbare := readRowCall_typeArgs_ne hrow (List.cons_ne_nil target rest).symm
      cases hhead : headOf s with
      | some head =>
        by_cases hprog : s ∈ programHeads
        · exact ⟨callRefusal head args, by simp only [readPerformFace, hhead, hprog, if_true]⟩
        · exact ⟨.unknownHead s, by simp only [readPerformFace, hhead, hprog, if_false]⟩
      | none => exact ⟨.arity s, by simp only [readPerformFace, hhead, hbare, Option.getD_some]⟩
  · next receiver s target rest args =>
    cases hsplit
    simp only [readPerformFace, readMethod, readRowMethod] at h
    obtain ⟨recv, hrecv, h⟩ := bind_eq_ok.mp h
    obtain ⟨body, hbody, _⟩ := bind_eq_ok.mp h
    cases hrow : readRowCall classes (methodSignature sig) spell n s (target :: rest) args with
    | none =>
      rw [hrow] at hbody
      cases hbody
    | some answer =>
      rw [hrow, Option.getD_some] at hbody
      subst hbody
      have hbare := readRowCall_typeArgs_ne hrow (List.cons_ne_nil target rest).symm
      exact ⟨.arity s, by
        simp only [readPerformFace, readMethod, readRowMethod, hrecv, hbare, Option.getD_some,
          ok_bind]
        rfl⟩
  · exact nomatch hsplit

/-- **A row's call with its operation's type arguments reads back**, to the operation at its
term's face: the operation with its own type arguments, and the unit literal for its binder
term. The premises are a readable request on a row in the signature's domain, and type arguments
that read back on that row (`typeArgsReadable`): each a readable type, on a call row that
declares none of its own. The row's call reads to the face (`read_printRow`), each printed type
reads to its type (`readTysChecked_of_readable`), and installing them in the face restores the
operation's own (`LawfulSpelling.withTypeArgs_face`). An operation that carries none prints its
row's call alone, with or without the row's declared type arguments on its head. A step of
`readPerform_printPerform`. It states nothing of a type outside `Classes.ReadableTy`. -/
theorem readCall_printCall {sig : Signature Op} {spell : String → List RowArg → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} {op : Op} {r : Term} (hd : sig.dom op = true)
    (hreq : requestReadable (sig.rowOf op) n r = true) (hc : r.covers classes = true)
    (hu : r.unannotated = true)
    (htypes : typeArgsReadable (sig.rowOf op) (sig.typeArgsOf op) = true)
    {x : Expr} (hp : printCall sig n op r = .ok x) :
    readCall classes sig spell n x = .ok (.perform (sig.withTerm op (.lit .unit)) r) := by
  unfold printCall at hp
  split at hp
  · next hnone =>
    -- no type argument of the operation's: the row's call alone, read at its face
    have hface := read_printRow hl op hd r hreq hc hu hp
    have hnil : sig.typeArgsOf (sig.face op) = [] :=
      List.eq_nil_of_length_eq_zero (by
        simp only [hl.length_typeArgsOf_face, hnone, List.length_nil])
    have hterm : sig.face op = sig.withTerm op (.lit .unit) := by
      rw [Signature.face, hl.typeArgs.withTypeArgs_none
        ((hl.typeArgs.typeArgsOf_withTerm op _).trans hnone)]
    have hfree : (readPerformFace classes sig spell n x).bind (typeFree sig) =
        .ok (.perform (sig.withTerm op (.lit .unit)) r) := by
      rw [hface]
      simp only [Except.bind, rowAnswer, typeFree, hnil, List.isEmpty_nil, if_true]
      rw [hterm]
    unfold readCall
    cases hsplit : splitHeadTypes x with
    | none => exact hfree
    | some split =>
      obtain ⟨bare, targets⟩ := split
      obtain ⟨why, hbare⟩ := readPerformFace_bare_error hsplit hface
      simp only [hbare]
      exact hfree
  · next ty tys htys =>
    split at hp
    · next targets hw =>
      cases hcall : printRow n (sig.rowOf op) r with
      | error why =>
        rw [hcall] at hp
        exact nomatch hp
      | ok call =>
        rw [hcall] at hp
        have hlen := Effect4.Codegen.Classes.writeTys_length hw
        cases targets with
        | nil => exact nomatch hlen
        | cons target rest =>
          have hsplit := splitHeadTypes_withHeadTypes hp
          have hface := read_printRow hl op hd r hreq hc hu hcall
          rw [htys] at htypes
          simp only [typeArgsReadable, Bool.and_eq_true] at htypes
          have hback := Effect4.Codegen.Classes.readTysChecked_of_readable htypes.1.1 hw
          have harity : (sig.typeArgsOf (sig.face op)).length = (target :: rest).length := by
            rw [hl.length_typeArgsOf_face, htys, hlen]
          unfold readCall
          rw [hsplit]
          dsimp only
          rw [hface]
          simp only [rowAnswer, installTypeArgs, harity, if_true, hback]
          rw [← htys, hl.withTypeArgs_face]
    · exact nomatch hp

/-- **The row call of `perform` reads back from its printing** at a node of level `n`: a
readable request on a row in the signature's domain, type arguments that read back on that row
(`typeArgsReadable`), and a binder term that reads back there (`termReadable`: scoped one level
up, covered, unannotated, on a call row). The row's call with its type arguments reads to the
operation at its term's face (`readCall_printCall`), the function's body to the term
(`readTerm_printTerm`), and installing the term gives the operation back
(`LawfulSpelling.withTerm_withTerm`, `withTerm_termOf`). A step of `read_print` (R8), the
row-call case of `readT_print` (`Laws/Codegen/ReadPrint.lean`). It states nothing of a term that
states an accumulator type, which is printed and not read, nor of a type argument outside
`Classes.ReadableTy`, nor of any host run. -/
theorem readPerform_printPerform {sig : Signature Op} {spell : String → List RowArg → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} {op : Op} {r : Term} (hd : sig.dom op = true)
    (hreq : requestReadable (sig.rowOf op) n r = true) (hc : r.covers classes = true)
    (hu : r.unannotated = true)
    (htypes : typeArgsReadable (sig.rowOf op) (sig.typeArgsOf op) = true)
    (hterm : termReadable classes n (sig.rowOf op) ((sig.termOf op).map (·.term)) = true)
    {x : Expr} (hp : printPerform sig n op r = .ok x) :
    readPerform classes sig spell n x = .ok (.perform op r) := by
  unfold printPerform at hp
  cases hb : sig.termOf op with
  | none =>
    rw [hb] at hp
    have hcall := readCall_printCall (classes := classes) hl hd hreq hc hu htypes hp
    rw [hl.withTerm_none op _ hb] at hcall
    unfold readPerform
    rw [splitFunction_printCall hp, hcall]
    simp only [termFree, hb, Option.isNone_none, ↓reduceIte]
  | some b =>
    rw [hb] at hp
    cases hcall : printCall sig n op r with
    | error why =>
      rw [hcall] at hp
      exact nomatch hp
    | ok call =>
      rw [hcall] at hp
      rw [hb, Option.map_some] at hterm
      simp only [termReadable, Bool.and_eq_true] at hterm
      obtain ⟨⟨⟨hscoped, hcovers⟩, hunannotated⟩, _⟩ := hterm
      have hsome : (sig.termOf (sig.withTerm op (.lit .unit))).isSome = true := by
        have h := hl.termOf_withTerm op (.lit .unit)
        rw [hb, Option.map_some] at h
        obtain ⟨b', hb', _⟩ := Option.map_eq_some_iff.mp h
        exact Option.isSome_iff_exists.mpr ⟨b', hb'⟩
      unfold readPerform
      rw [splitFunction_withFunction hp]
      simp only [readCall_printCall hl hd hreq hc hu htypes hcall, ok_bind,
        readTerm_printTerm b.term hscoped hcovers hunannotated, installTerm, hsome, ↓reduceIte]
      rw [hl.withTerm_withTerm, hl.withTerm_termOf op b hb]

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
theorem readRowCall_method_parts {sig : Signature Op} {spell : String → List RowArg → Option Op}
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
      rw [rowArgs?_exact hn]
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
            Option.bind_eq_some_iff.mp ‹(rowArgs? _).bind (spell s) = some _›
          obtain ⟨hs, htr⟩ := hl.row_of_spell _ _ _ hsp
          refine ⟨_, r, rfl, hs, hc.2.2, ?_⟩
          rw [rowArgs?_exact hn]
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
                Option.bind_eq_some_iff.mp ‹(rowArgs? _).bind (spell s) = some _›
              obtain ⟨hs, htr⟩ := hl.row_of_spell _ _ _ hsp
              refine ⟨_, r, rfl, hs, hc.2, ?_⟩
              rw [rowArgs?_exact hn]
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

theorem readRowMethod_exact {sig : Signature Op} {spell : String → List RowArg → Option Op}
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

theorem readMethod_exact {sig : Signature Op} {spell : String → List RowArg → Option Op}
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
from `rowArgs?_exact`, and the request from its reader's exactness. -/
theorem readRowCall_exact {sig : Signature Op} {spell : String → List RowArg → Option Op}
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
      rw [print_rowAnswer, rowArgs?_exact hnames]
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
            Option.bind_eq_some_iff.mp ‹(rowArgs? _).bind (spell s) = some _›
          obtain ⟨hs, htr⟩ := hl.row_of_spell _ _ _ hsp
          rw [print_rowAnswer, rowArgs?_exact hnames]
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
                Option.bind_eq_some_iff.mp ‹(rowArgs? _).bind (spell s) = some _›
              obtain ⟨hs, htr⟩ := hl.row_of_spell _ _ _ hsp
              rw [print_rowAnswer, rowArgs?_exact hnames]
              cases ta <;>
                simp [rowCallImage, printRow, printRowHead, hshape.1, hshape.2, hs, htr,
                  readTupleArgs_exact hr]
            · cases h
          · cases h
        · cases h
    · cases h

/-- A bare identifier read as a value row prints back. -/
theorem readRowValue_exact {sig : Signature Op} {spell : String → List RowArg → Option Op}
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
theorem readPerformFace_exact {sig : Signature Op} {spell : String → List RowArg → Option Op}
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
  obtain ⟨split, hsplit, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨body', hbody, h⟩ := Option.map_eq_some_iff.mp h
  cases h
  unfold lastArgument? at hsplit
  split at hsplit
  · next head args =>
    obtain ⟨last, hlast, hsplit⟩ := Option.map_eq_some_iff.mp hsplit
    cases hsplit
    obtain ⟨front, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
    rw [Effect4.Codegen.Binders.read_exact n [0] last body hbody, List.dropLast_concat]
    rfl
  · next receiver name args =>
    obtain ⟨last, hlast, hsplit⟩ := Option.map_eq_some_iff.mp hsplit
    cases hsplit
    obtain ⟨front, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
    rw [Effect4.Codegen.Binders.read_exact n [0] last body hbody, List.dropLast_concat]
    rfl
  · exact nomatch hsplit

/-- An operation's binder term does not move its row's call or its type arguments, so the
call prints alike with any term. A step of `readPerform_exact`. -/
theorem printCall_withTerm {sig : Signature Op} {spell : String → List RowArg → Option Op}
    (hl : LawfulSpelling sig spell) (n : Nat) (op : Op) (f : Term) (r : Term) :
    printCall sig n (sig.withTerm op f) r = printCall sig n op r := by
  unfold printCall
  rw [hl.typeArgs.typeArgsOf_withTerm, hl.withTerm_row]

/-- A face that carries no type argument of the operation's prints as its row's call. A step
of `readCall_exact`, at both of its readings of a call whose type arguments are not the
operation's. -/
theorem typeFree_exact {sig : Signature Op} {spell : String → List RowArg → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} {x : Expr} {e : Eff Op}
    (h : (readPerformFace classes sig spell n x).bind (typeFree sig) = .ok e) :
    ∃ op r, e = .perform op r ∧ printCall sig n op r = .ok x := by
  cases hface : readPerformFace classes sig spell n x with
  | error why =>
    rw [hface] at h
    exact nomatch h
  | ok face =>
    rw [hface] at h
    have hx := readPerformFace_exact hl hface
    cases face with
    | perform op r =>
      have hrow : printRow n (sig.rowOf op) r = .ok x := hx
      simp only [Except.bind, typeFree] at h
      split at h
      · next hnil =>
        cases h
        refine ⟨op, r, rfl, ?_⟩
        unfold printCall
        rw [List.isEmpty_iff.mp hnil]
        exact hrow
      · exact nomatch h
    | _ => exact nomatch h

/-- **Exactness of the row call with its type arguments**: what `readCall` accepts is a
`perform`, and the printer prints it back to the tree read. Where the head's type arguments were
the operation's, each read type prints back to its spelling (`readTysChecked_exact`: the checked
reader keeps only what the type printer prints back), the installed list is the operation's
(`LawfulTypeArgs.typeArgsOf_withTypeArgs`), and the restored operation's row prints the call
that the face's row prints, because the two rows have the same call columns
(`LawfulTypeArgs.call`, `printRow_congr`). It asks for no readable-type premise. A step of
`readPerform_exact`. -/
theorem readCall_exact {sig : Signature Op} {spell : String → List RowArg → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} {x : Expr} {e : Eff Op}
    (h : readCall classes sig spell n x = .ok e) :
    ∃ op r, e = .perform op r ∧ printCall sig n op r = .ok x := by
  unfold readCall at h
  split at h
  · next bare targets hsplit =>
    split at h
    · next face hface =>
      have hx := readPerformFace_exact hl hface
      cases face with
      | perform op r =>
        have hrow : printRow n (sig.rowOf op) r = .ok bare := hx
        simp only [installTypeArgs] at h
        split at h
        · next harity =>
          split at h
          · next tys htys =>
            cases h
            refine ⟨_, r, rfl, ?_⟩
            have hlen := Effect4.Codegen.Classes.readTysChecked_length htys
            have hargs := hl.typeArgs.typeArgsOf_withTypeArgs op tys (hlen.trans harity.symm)
            have hw := Effect4.Codegen.Classes.readTysChecked_exact htys
            cases tys with
            | nil =>
              have hnil : targets = [] := List.eq_nil_of_length_eq_zero hlen.symm
              exact absurd hnil (splitHeadTypes_ne_nil hsplit)
            | cons ty rest =>
              unfold printCall
              rw [hargs]
              dsimp only
              rw [hw]
              dsimp only
              rw [printRow_congr (hl.typeArgs.call op (ty :: rest)), hrow]
              exact withHeadTypes_of_splitHeadTypes _ hsplit
          · exact nomatch h
        · exact nomatch h
      | _ => exact nomatch h
    · exact typeFree_exact hl h
  · exact typeFree_exact hl h

/-- The row call of `perform`: what `readPerform` accepts prints back to the tree it read. The
call it reads prints back with its type arguments (`readCall_exact`). Where a function follows
the call's arguments, its body is the term the reader installed (`readTerm_exact`), the printer
prints that term as the same function (`Binders.read_exact`) after the same call, since the
call does not depend on the term (`printCall_withTerm`). Where none follows, the operation
carries no term, and the printer prints the call alone. A step of `read_exact` (R8). -/
theorem readPerform_exact {sig : Signature Op} {spell : String → List RowArg → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} {x : Expr} {e : Eff Op}
    (h : readPerform classes sig spell n x = .ok e) : print sig n e = .ok x := by
  unfold readPerform at h
  split at h
  · next call body hsplit =>
    obtain ⟨typed, htyped, h⟩ := bind_eq_ok.mp h
    obtain ⟨f, hf, h⟩ := bind_eq_ok.mp h
    obtain ⟨op, r, rfl, hcall⟩ := readCall_exact hl htyped
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
      rw [printCall_withTerm hl, hcall, hbt, readTerm_exact body hf]
      exact withFunction_of_splitFunction _ hsplit
    · exact nomatch h
  · next hsplit =>
    cases htyped : readCall classes sig spell n x with
    | error why =>
      rw [htyped] at h
      exact nomatch h
    | ok typed =>
      rw [htyped] at h
      obtain ⟨op, r, rfl, hcall⟩ := readCall_exact hl htyped
      simp only [termFree] at h
      split at h
      · next hnone =>
        cases h
        rw [print_perform, printPerform, Option.isNone_iff_eq_none.mp hnone]
        exact hcall
      · exact nomatch h

end ReadExact

end Rows

/-- A string is among the names of a row's trailing arguments exactly when it is one of them. -/
theorem RowArg.mem_names {args : List RowArg} {s : String} :
    s ∈ RowArg.names args ↔ RowArg.name s ∈ args := by
  simp only [RowArg.names, List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, hs⟩
    cases a with
    | name t =>
      simp only [RowArg.name?, Option.some.injEq] at hs
      subst hs
      exact ha
    | str v => simp only [RowArg.name?, reduceCtorEq] at hs
  · intro h
    exact ⟨_, h, rfl⟩

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
trailing name: the faces print its term as a function. `Deferred.make`'s row declares no type
argument: the faces print the operation's own on the call's head. -/
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
  | call k =>
    exact (by decide : (NativeOp.callPlaceholder.shape = .value →
      NativeOp.callPlaceholder.trailing = []) ∧ rowNamesSafe NativeOp.callPlaceholder = true)
  | _ => decide

/-- The three checks of a lawful table: the program plane's, the names', and the literals'. -/
theorem lawfulTable_parts {table : RowTable} (h : LawfulTable table = true) :
    Table.lawful table = true ∧ table.all rowNamesSafe = true ∧
      literalsAlone (nativeRows table) = true := by
  simp only [LawfulTable, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem lawfulTable_member (table : RowTable) (h : LawfulTable table = true)
    (row : Row) (hr : row ∈ table) :
    rowKey row ∉ builtinKeys ∧
    (row.shape = .value → row.trailing = []) ∧ rowNamesSafe row = true := by
  obtain ⟨hlaw, hsafe, _⟩ := lawfulTable_parts h
  simp only [Table.lawful, Bool.and_eq_true] at hlaw
  refine ⟨?_, ?_, List.all_eq_true.mp hsafe row hr⟩
  · have hc := List.all_eq_true.mp hlaw.1.2 row hr
    simpa [Row.key] using hc
  · have hv := List.all_eq_true.mp hlaw.2 row hr
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

/-- Rows with the same call columns print their requests alike. -/
theorem Row.printsRequest_callColumns {a b : Row} (h : a.callColumns = b.callColumns) :
    a.printsRequest = b.printsRequest := by
  simp only [Row.printsRequest, Row.callColumns_shape h, Row.callColumns_request h]

/-- A row that prints no request prints none once its types are normal: `unit` is normal. -/
theorem Row.printsRequest_normalizeTypes {row : Row} (h : row.printsRequest = false) :
    row.normalizeTypes.printsRequest = false := by
  obtain ⟨name, spelling, shape, trailing, kind, request, answer, error, requires, cite,
    typeArgs, registration⟩ := row
  cases shape with
  | value => rfl
  | call =>
    change (!decide (request = Ty.unit)) = false at h
    have hu : request = Ty.unit := of_decide_eq_true (by
      cases hr : decide (request = Ty.unit) with
      | false => rw [hr] at h; exact nomatch h
      | true => rfl)
    subst hu
    have hn : Ty.normalize Ty.unit = Ty.unit := by simp only [Ty.normalize]
    change (!decide (Ty.normalize Ty.unit = Ty.unit)) = false
    rw [hn]
    decide
  | tupleCall => exact nomatch h
  | method => exact nomatch h

/-- Every built-in operation has the call columns of its key's representative in
`NativeOp.spelled`: a term row's at the unit literal, `Deferred.make`'s at `(nat, nat)`, and
every other operation its own. -/
theorem NativeOp.callColumns_spelled (op : NativeOp) (h : ∀ i, op ≠ .external i)
    (hc : ∀ k, op ≠ .call k) :
    ∃ rep ∈ NativeOp.spelled, rep.row.callColumns = op.row.callColumns := by
  cases op with
  | external i => exact absurd rfl (h i)
  | call k => exact absurd rfl (hc k)
  | refUpdateWith f => exact ⟨.refUpdateWith (.lit .unit), by decide, rfl⟩
  | refGetAndUpdateWith f => exact ⟨.refGetAndUpdateWith (.lit .unit), by decide, rfl⟩
  | refUpdateAndGetWith f => exact ⟨.refUpdateAndGetWith (.lit .unit), by decide, rfl⟩
  | refUpdateSomeWith f => exact ⟨.refUpdateSomeWith (.lit .unit), by decide, rfl⟩
  | refGetAndUpdateSomeWith f => exact ⟨.refGetAndUpdateSomeWith (.lit .unit), by decide, rfl⟩
  | refUpdateSomeAndGetWith f => exact ⟨.refUpdateSomeAndGetWith (.lit .unit), by decide, rfl⟩
  | refModifyWith f => exact ⟨.refModifyWith (.lit .unit), by decide, rfl⟩
  | refModifySomeWith f => exact ⟨.refModifySomeWith (.lit .unit), by decide, rfl⟩
  | deferredMakeOf value error => exact ⟨.deferredMakeOf .nat .nat, by decide, rfl⟩
  | scopeMake s => exact ⟨.scopeMake s, by cases s <;> decide, rfl⟩
  | _ => exact ⟨_, by decide, rfl⟩

/-- A built-in operation has the call columns of its representative's row in `nativeRows`. -/
theorem nativeRows_rep_builtin (table : RowTable) (op : NativeOp) (h : ∀ i, op ≠ .external i)
    (hc : ∀ k, op ≠ .call k) :
    ∃ r ∈ nativeRows table, r.callColumns = (nativeRowOf table op).callColumns := by
  obtain ⟨rep, hm, heq⟩ := NativeOp.callColumns_spelled op h hc
  rw [nativeRowOf_builtin table op h]
  exact ⟨rep.row, List.mem_append_left _ (List.mem_map_of_mem hm), heq⟩

/-- An operation of the native signature that is no invocation and no external index past the
table has the call columns of a row of `nativeRows`. -/
theorem nativeRows_rep (table : RowTable) (op : NativeOp)
    (hext : ∀ i, op = .external i → i < table.length) (hc : ∀ k, op ≠ .call k) :
    ∃ r ∈ nativeRows table, r.callColumns = (nativeRowOf table op).callColumns := by
  cases op with
  | external i =>
    have hi := hext i rfl
    rw [nativeRowOf_external table i hi]
    exact ⟨table[i], List.mem_append_right _ (List.getElem_mem hi), rfl⟩
  | call k => exact absurd rfl (hc k)
  | _ => exact nativeRows_rep_builtin table _ (by intro i he; cases he) (by intro k he; cases he)

/-- What `nativeSpell` answers is a row of `nativeRows` with the key it was asked: a built-in
representative's or the table's. -/
theorem nativeSpell_mem (table : RowTable) {s : String} {names : List RowArg} {op : NativeOp}
    (h : nativeSpell table s names = some op) :
    ∃ r ∈ nativeRows table, r.spelling = s ∧ r.trailing = names := by
  unfold nativeSpell at h
  split at h
  · rename_i found hfound
    have hm := List.mem_of_find?_eq_some hfound
    have hk := List.find?_some
      (p := fun op : NativeOp => decide (rowKey op.row = (s, names))) hfound
    exact ⟨found.row, List.mem_append_left _ (List.mem_map_of_mem hm),
      Prod.mk.inj (of_decide_eq_true hk)⟩
  · obtain ⟨i, hi, _⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hlt, hk⟩ := rowIndex_exact table (s, names) i hi
    exact ⟨table[i], List.mem_append_right _ (List.getElem_mem hlt), Prod.mk.inj hk⟩

/-- An operation of the native signature's domain is no placeholder. -/
theorem nativeRows_rep_of_dom (table : RowTable) (op : NativeOp)
    (hd : (nativeSignature table).dom op = true) :
    ∃ r ∈ nativeRows table, r.callColumns = (nativeRowOf table op).callColumns := by
  refine nativeRows_rep table op ?_ ?_
  · intro i he
    subst he
    exact of_decide_eq_true hd
  · intro k he
    subst he
    exact absurd hd Bool.false_ne_true

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
        have hlaw := (lawfulTable_parts h).1
        simp only [Table.lawful, Bool.and_eq_true, decide_eq_true_eq] at hlaw
        exact hlaw.1.1
      have hc := (lawfulTable_member table h _ (List.getElem_mem hi)).1
      have hb := builtinLookup_none (rowKey table[i]) hc
      have hf := rowIndex_roundTrip table hn i hi
      dsimp +instances only [rowKey] at hb hf
      unfold nativeSpell rowKey
      rw [hb, hf]
      rfl
    | scopeMake s => cases s <;> rfl
    -- `Deferred.make`: its key names the row alone, and the spelling reads its face back, the
    -- instance that `NativeOp.spelled` holds, whatever type arguments the operation carries
    | deferredMakeOf value error => rfl
    -- an invocation is outside the native signature's domain: only a block's signature has it
    | call k => exact absurd hd Bool.false_ne_true
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
    intro op i hm
    have hn := (nativeRow_hygiene table h op).2
    simp only [rowNamesSafe, Bool.and_eq_true] at hn
    have hn := hn.1
    refine name_notin (RowArg.names (nativeRowOf table op).trailing) ?_ i (RowArg.mem_names.mpr hm)
    intro name hm
    have ht := List.all_eq_true.mp hn.2 name hm
    simpa only [firstByte, bne_iff_ne, ne_eq, Bool.not_eq_true] using
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ht).1).1
  trailing_ne_undefined := by
    intro op hm
    have hn := (nativeRow_hygiene table h op).2
    simp only [rowNamesSafe, Bool.and_eq_true] at hn
    have hn := hn.1
    have ht := List.all_eq_true.mp hn.2 "undefined" (RowArg.mem_names.mpr hm)
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
  -- an operation's type arguments: the call columns of its row do not depend on them, replacing
  -- them is an exact update at the operation's arity, and the update is independent of the term's
  typeArgs :=
    { call := by
        intro op tys
        cases op with
        | deferredMakeOf value error => rcases tys with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> rfl
        | _ => rfl
      typeArgsOf_withTypeArgs := NativeOp.typeArgs_withTypeArgs
      length_typeArgsOf := NativeOp.length_typeArgs_withTypeArgs
      withTypeArgs_typeArgsOf := NativeOp.withTypeArgs_typeArgs
      withTypeArgs_withTypeArgs := NativeOp.withTypeArgs_withTypeArgs
      withTypeArgs_withTerm := fun op tys f => NativeOp.withTypeArgs_withTerm op tys f
      termOf_withTypeArgs := by
        intro op tys
        change ((op.withTypeArgs tys).binder?.map fun b =>
            (⟨b.2, b.1.param, b.1.result⟩ : BinderTerm)).map (·.term) =
          (op.binder?.map fun b => (⟨b.2, b.1.param, b.1.result⟩ : BinderTerm)).map (·.term)
        rw [NativeOp.binder?_withTypeArgs]
      typeArgsOf_withTerm := NativeOp.typeArgs_withTerm }
  -- a key that begins with a literal is a row of `nativeRows` (`Scope.make("parallel")`'s);
  -- the table's check decides that no row of its spelling there prints a request
  literal_alone := by
    intro op v names hd hp
    cases hsp : nativeSpell table ((nativeSignature table).rowOf op).spelling (.str v :: names)
    with
    | none => rfl
    | some found =>
      exfalso
      obtain ⟨r, hr, hs, htr⟩ := nativeSpell_mem table hsp
      obtain ⟨r', hr', hrc'⟩ := nativeRows_rep_of_dom table op hd
      have hall := List.all_eq_true.mp (lawfulTable_parts h).2.2 r hr
      have hhead : r.literalHead = true := by simp only [Row.literalHead, htr]
      simp only [hhead, Bool.not_true, Bool.false_or] at hall
      have hmate := List.all_eq_true.mp hall r' hr'
      have hspell : r'.spelling = r.spelling := (Row.callColumns_spelling hrc').trans hs.symm
      simp only [hspell, bne_self_eq_false, Bool.false_or, Bool.not_eq_true'] at hmate
      have hraw := (Row.printsRequest_callColumns hrc').symm.trans hmate
      have hno : ((nativeSignature table).rowOf op).printsRequest = false :=
        Row.printsRequest_normalizeTypes hraw
      exact nomatch hp.symm.trans hno

end Effect4.Program
