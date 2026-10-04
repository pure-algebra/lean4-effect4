import Effect4.Codegen.Read
import Effect4.Laws.Codegen.Record
import Effect4.Laws.Codegen.Tuple
import Effect4.Laws.Codegen.Classes

/-!
# Leaf and row reconstruction laws

Concept: Exact Codecs & Data Plane Embeddings. Claim served: `printed-modules` (R2/R3).
The term retraction keeps scope as its premise, and, since the payload class face (decisions row
120, part E2), coverage: the module's classes declare every class construction's fields
(`Term.covers`). Exactness assumes successful reading under any classes. These declarations moved
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

mutual
  /-- **The term round trip** (`collection-term-print-read`): a scoped term whose class
  constructions the classes cover reads back from its printing. Since decisions row 120, part E2,
  a class construction prints as `new Tag({ … })` and reads back from the module's classes, with
  `_tag` restored first (`Classes.classTag?`); placed at R8 (`translation-simulation`) as a step of
  `read_print`, and at R3 as the record terms' printed form. -/
  theorem readTerm_printTerm {classes : Classes} {n : Nat} (t : Term)
      (h : Term.scoped n t = true) (hc : t.covers classes = true) :
      readTerm classes n (printTerm t) = .ok t :=
    match t, h, hc with
    | .var i, h, _ => by
      simp only [Term.scoped, decide_eq_true_eq] at h
      simp only [printTerm, readTerm, Effect4.Codegen.Classes.readClass,
        Effect4.Codegen.Record.readRecord, Effect4.Codegen.Record.readField,
        Effect4.Codegen.Record.readSet, Effect4.Codegen.Tuple.readAt, Var.read_name h]
    | .lit .unit, _, _ => by
      simp only [printTerm, printLit, readTerm, Effect4.Codegen.Classes.readClass,
        Effect4.Codegen.Record.readRecord, Effect4.Codegen.Record.readField,
        Effect4.Codegen.Record.readSet, Effect4.Codegen.Tuple.readAt,
        Var.read_none Var.name_ne_undefined, ↓reduceIte]
    | .lit (.nat k), _, _ => by
      rw [printTerm, printLit, readTerm]
      rfl
    | .lit (.bool b), _, _ => by rw [printTerm, printLit, readTerm]; rfl
    | .lit (.str s), _, _ => by rw [printTerm, printLit, readTerm]; rfl
    | .app atom args, h, hc => by
      simp only [Term.scoped] at h
      rw [Term.covers_app] at hc
      simp only [printTerm, readTerm, Effect4.Codegen.Classes.readClass,
        Effect4.Codegen.Record.readRecord, Effect4.Codegen.Record.readField,
        Effect4.Codegen.Record.readSet, Effect4.Codegen.Tuple.readAt,
        readTerms_printTerms args h hc, Except.map]
    | .record fields names values, h, hc => by
      simp only [Term.scoped] at h
      rw [Term.covers_record, Bool.and_eq_true] at hc
      obtain ⟨hnode, hvals⟩ := hc
      have hr := readTerms_printTerms values h hvals
      rw [printTerm]
      cases hct : Effect4.Codegen.Classes.classTag? fields names values with
      | some tag =>
        obtain ⟨_, _, hnames, hvalues, _, hlen⟩ := Effect4.Codegen.Classes.classTag?_some hct
        have hlookup := coverNode_class hnode hct
        have htail : readTerms classes n (printTerms (Effect4.Codegen.Classes.restTerms values)) =
            .ok (Effect4.Codegen.Classes.restTerms values) := by
          rw [hvalues] at hr
          simp only [printTerms, readTerms, bind_eq_ok] at hr
          obtain ⟨t', _, ts', hts', hcons⟩ := hr
          simp only [Except.ok.injEq, Terms.cons.injEq] at hcons
          rw [hcons.2] at hts'
          exact hts'
        have hlen' : names.tail.length = (printTerms values).tail.length := by
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
        · have hs := Effect4.Codegen.Record.readRecord_writeRecord fields names (printTerms values)
          split
          · next fields' names' values' hrec =>
            rw [hrec] at hs
            cases hs
            rw [hr, ok_bind, hct]
            rfl
          · next hrec => rw [hrec] at hs; exact nomatch hs
    | .field mode target name, h, hc => by
      simp only [Term.scoped] at h
      rw [Term.covers_field] at hc
      rw [printTerm, readTerm]
      split
      · next tag' names' values' hcls =>
        rw [Effect4.Codegen.Classes.readClass_writeField] at hcls; exact nomatch hcls
      · have hr0 := Effect4.Codegen.Record.readRecord_writeField
          (decide (mode = .optional)) name (printTerm target)
        split
        · next fields names values hr => rw [hr] at hr0; exact nomatch hr0
        ·
          have hs := Effect4.Codegen.Record.readField_writeField
            (decide (mode = .optional)) name (printTerm target)
          split
          · next optional name' target' hf =>
            rw [hf] at hs
            cases hs
            rw [readTerm_printTerm target h hc]
            cases mode <;> rfl
          · next hf => rw [hf] at hs; exact nomatch hs
    | .recordSet target name value, h, hc => by
      simp only [Term.scoped, Bool.and_eq_true] at h
      rw [Term.covers_recordSet, Bool.and_eq_true] at hc
      rw [printTerm, readTerm]
      split
      · next tag' names' values' hcls =>
        rw [Effect4.Codegen.Classes.readClass_writeSet] at hcls; exact nomatch hcls
      · simp only [Effect4.Codegen.Record.readRecord_writeSet,
          Effect4.Codegen.Record.readField_writeSet]
        have hs := Effect4.Codegen.Record.readSet_writeSet name (printTerm target) (printTerm value)
        split
        · next name' target' value' hr =>
          rw [hr] at hs
          cases hs
          rw [readTerm_printTerm target h.1 hc.1]
          simp only [ok_bind, readTerm_printTerm value h.2 hc.2]
        · next hr => rw [hr] at hs; exact nomatch hs
    | .tupleAt target index, h, hc => by
      simp only [Term.scoped] at h
      rw [Term.covers_tupleAt] at hc
      rw [printTerm, readTerm]
      split
      · next tag' names' values' hcls =>
        rw [Effect4.Codegen.Classes.readClass_writeAt] at hcls; exact nomatch hcls
      · simp only [Effect4.Codegen.Tuple.readRecord_writeAt,
          Effect4.Codegen.Tuple.readField_writeAt, Effect4.Codegen.Tuple.readSet_writeAt]
        have hs := Effect4.Codegen.Tuple.readAt_writeAt index (printTerm target)
        split
        · next index' target' hr =>
          rw [hr] at hs
          cases hs
          rw [readTerm_printTerm target h hc]
          rfl
        · next hr => rw [hr] at hs; exact nomatch hs
  termination_by structural t

  theorem readTerms_printTerms {classes : Classes} {n : Nat} (ts : Terms)
      (h : Terms.scoped n ts = true) (hc : ts.covers classes = true) :
      readTerms classes n (printTerms ts) = .ok ts :=
    match ts, h, hc with
    | .nil, _, _ => by rw [printTerms, readTerms]
    | .cons t ts, h, hc => by
      simp only [Terms.scoped, Bool.and_eq_true] at h
      rw [Terms.covers_cons, Bool.and_eq_true] at hc
      simp only [printTerms, readTerms, readTerm_printTerm t h.1 hc.1,
        readTerms_printTerms ts h.2 hc.2, ok_bind]
  termination_by structural ts
end

mutual
  /-- **Term exactness**: what the term reader accepts, under any classes, prints back to
  exactly the expression it read. A class construction is accepted only when the printer prints
  the term it reads to as that construction, and a structural record only when it does not.
  Placed at R8 (`translation-simulation`) as a step of `read_exact`. -/
  theorem readTerm_exact {classes : Classes} {n : Nat} (x : Expr) {t : Term}
      (h : readTerm classes n x = .ok t) : printTerm t = x := by
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
      (h : readTerms classes n xs = .ok ts) : printTerms ts = xs := by
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
  have ht := readTerm_printTerm (classes := []) (n := 0) (.lit value) rfl (Term.covers_lit_nil value)
  change readTerm [] 0 (printLit value) = .ok (.lit value) at ht
  rw [ht]
  rfl

theorem readLiteral_exact {x : Expr} {value : Lit} (h : readLiteral x = .ok value) :
    printLit value = x := by
  simp only [readLiteral, bind_eq_ok] at h
  obtain ⟨term, ht, h⟩ := h
  cases term with
  | var _ | app _ _ | record _ _ _ | field _ _ _ | recordSet _ _ _ | tupleAt _ _ => cases h
  | lit v =>
    cases h
    exact readTerm_exact x ht

/-! ## Causes, fork options, rows: the small round trips -/

section Rows

variable {classes : Classes}


theorem headOf_lit (h : Head) (s : String) (hs : h.spelling = s) : headOf s = some h :=
  hs ▸ headOf_spelling h

theorem readCause_printCause {n : Nat} (c : CauseTerm) (h : CauseTerm.scoped n c = true)
    (hc : c.covers classes = true) : readCause classes n (printCause c) = .ok c := by
  induction c with
  | fail e =>
    simp only [CauseTerm.scoped] at h
    rw [CauseTerm.covers_fail] at hc
    rw [printCause]; unfold readCause; simp [headOf_lit .causeFail "Cause.fail" rfl, readTerm_printTerm e h hc]
  | die d =>
    simp only [CauseTerm.scoped] at h
    rw [CauseTerm.covers_die] at hc
    rw [printCause]; unfold readCause; simp [headOf_lit .causeDie "Cause.die" rfl, readTerm_printTerm d h hc]
  | interrupt who =>
    cases who with
    | none => rw [printCause]; unfold readCause; simp [headOf_lit .causeInterrupt "Cause.interrupt" rfl]
    | some w =>
      simp only [CauseTerm.scoped] at h
      rw [CauseTerm.covers_interrupt, Option.all_some] at hc
      rw [printCause]; unfold readCause; simp [headOf_lit .causeInterrupt "Cause.interrupt" rfl, readTerm_printTerm w h hc]
  | both l r ihl ihr =>
    simp only [CauseTerm.scoped, Bool.and_eq_true] at h
    rw [CauseTerm.covers_both, Bool.and_eq_true] at hc
    rw [printCause]; unfold readCause; simp [headOf_lit .causeCombine "Cause.combine" rfl, ihl h.1 hc.1, ihr h.2 hc.2]

theorem readCause_exact {n : Nat} (x : Expr) {c : CauseTerm} (h : readCause classes n x = .ok c) :
    printCause c = x := by
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

theorem idents?_printTerms : ∀ ts : Terms, idents? (printTerms ts) = ts.names?
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

theorem printTerm_ident {t : Term} {x : String} (h : printTerm t = .ident x) :
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

theorem printTerm_eq_bool (term : Term) (value : Bool) :
    printTerm term = .bool value ↔ term = .lit (.bool value) := by
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

/-- An atom application that is no row reads as no row call, so the caller may read it as a
term. -/
theorem readRowCall_none {sig : Signature Op} {spell : String → List String → Option Op} {n : Nat}
    {atom : String} {args : Terms} (h : noRow spell atom args = true) :
    readRowCall classes sig spell n atom [] (printTerms args) = none := by
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

theorem readRowCall_unit {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true)
    (hshape : (sig.rowOf op).shape = .call) (hreq : (sig.rowOf op).request = Ty.unit)
    {typeArgs : List TypeScript.TypeRef}
    (hta : rowTypeArgs (sig.rowOf op) = some typeArgs) :
    readRowCall classes sig spell n (sig.rowOf op).spelling typeArgs
        ((sig.rowOf op).trailing.map Expr.ident)
      = some (.ok (rowAnswer (sig.rowOf op) op (.lit .unit))) := by
  unfold readRowCall
  rw [idents?_map, Option.bind_some, hl.spell_row op hd]
  simp [hshape, hreq, hta]

theorem readRowCall_request {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true) (r : Term)
    (hshape : (sig.rowOf op).shape = .call) (hreq : (sig.rowOf op).request ≠ Ty.unit)
    {typeArgs : List TypeScript.TypeRef}
    (hta : rowTypeArgs (sig.rowOf op) = some typeArgs) :
    readRowCall classes sig spell n (sig.rowOf op).spelling typeArgs
        (printTerm r :: (sig.rowOf op).trailing.map Expr.ident)
      = some ((readTerm classes n (printTerm r)).map (rowAnswer (sig.rowOf op) op)) := by
  have key : ∀ x, (∀ op', x ∉ (sig.rowOf op').trailing) →
      spell (sig.rowOf op).spelling (x :: (sig.rowOf op).trailing) = none := by
    intro x hx
    cases hsp : spell (sig.rowOf op).spelling (x :: (sig.rowOf op).trailing) with
    | none => rfl
    | some op' =>
      exfalso
      obtain ⟨_, htr⟩ := hl.row_of_spell _ _ _ hsp
      exact hx op' (htr ▸ List.mem_cons_self)
  have hA : ((idents? (printTerm r :: (sig.rowOf op).trailing.map Expr.ident)).bind
      (spell (sig.rowOf op).spelling)) = none := by
    cases he : printTerm r with
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
  rw [idents?_map, Option.bind_some, hl.spell_row op hd]
  simp [hshape, hreq, hta]

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
theorem printTerm_ident_not_trailing {sig : Signature Op}
    {spell : String → List String → Option Op} (hl : LawfulSpelling sig spell) (r : Term)
    (op : Op) (v : String) (h : printTerm r = .ident v) : v ∉ (sig.rowOf op).trailing := by
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
      = some ((readTupleArgs classes n x y).map (rowAnswer (sig.rowOf op) op)) := by
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
  rw [idents?_map, Option.bind_some, hl.spell_row op hd]
  simp [hshape, hta]

/-- The tuple request round trip is shared by free calls and receiver methods. -/
theorem readRowCall_printTupleArgs {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true)
    (hshape : (sig.rowOf op).shape = .tupleCall) (r : Term)
    (h : tupleRequestReadable n r = true) (hc : r.covers classes = true)
    {typeArgs : List TypeScript.TypeRef}
    (hta : rowTypeArgs (sig.rowOf op) = some typeArgs) :
    readRowCall classes sig spell n (sig.rowOf op).spelling typeArgs
      (printTupleArgs r ++ (sig.rowOf op).trailing.map Expr.ident) =
      some (.ok (rowAnswer (sig.rowOf op) op r)) := by
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
        readTerm_printTerm (.var i) h rfl
      simp [readTupleArgs, savedVar?, hv]
    | lit value =>
      cases value with
      | unit =>
        simp only [printTupleArgs, hpa, printTerm, printLit, List.cons_append, List.nil_append]
        rw [readRowCall_tuple hl op hd _ _ hshape
          (fun _ _ hx => by cases hx) (fun _ _ hy => by cases hy) hta]
        have hv : readTerm classes n (.ident "undefined") = .ok (.lit .unit) :=
          readTerm_printTerm (.lit .unit) rfl rfl
        simp [readTupleArgs, savedVar?, hv]
      | nat _ | bool _ | str _ => simp at h
    | app _ _ | record _ _ _ | field _ _ _ | recordSet _ _ _ | tupleAt _ _ => cases h
  · simp only [hpa, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    obtain ⟨⟨hx, hy⟩, hsv⟩ := h
    obtain rfl := pairArgs?_some hpa
    rw [Term.covers_app, Terms.covers_cons, Terms.covers_cons, Bool.and_eq_true,
      Bool.and_eq_true] at hc
    simp only [printTupleArgs, hpa, List.cons_append, List.nil_append]
    rw [readRowCall_tuple hl op hd _ _ hshape
      (fun op' v hv => printTerm_ident_not_trailing hl x op' v hv)
      (fun op' v hv => printTerm_ident_not_trailing hl y op' v hv) hta]
    simp [readTupleArgs, hsv, readTerm_printTerm x hx hc.1, readTerm_printTerm y hy hc.2.1]

/-- Method projection keeps the same row identities and name hygiene. -/
theorem methodLawful {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) : LawfulSpelling (methodSignature sig) spell where
  spell_row := hl.spell_row
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

theorem readRowCall_methodArgs {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true) (args : Term)
    (h : (if (methodArgsRow (sig.rowOf op)).shape = .tupleCall then tupleRequestReadable n args
      else if (methodArgsRow (sig.rowOf op)).request = Ty.unit then decide (args = .lit .unit)
      else args.scoped n) = true) (hc : args.covers classes = true)
    {typeArgs : List TypeScript.TypeRef}
    (hta : rowTypeArgs (sig.rowOf op) = some typeArgs) :
    readRowCall classes (methodSignature sig) spell n (sig.rowOf op).spelling typeArgs
      (printMethodArgs (sig.rowOf op) args) = some (.ok (rowAnswer (sig.rowOf op) op args)) := by
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
      rw [readTerm_printTerm args h hc] at result
      simp only [map_ok] at result
      dsimp +instances only [methodSignature, methodArgsRow, rowAnswer] at result ⊢
      exact result
  · simp only [hs, if_true] at h
    simp only [printMethodArgs, hs, if_true]
    have result := readRowCall_printTupleArgs (classes := classes) (n := n) hm op hd hs args h hc hta
    dsimp +instances only [methodSignature, methodArgsRow, rowAnswer] at result ⊢
    exact result

theorem readRowMethod_print {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true)
    (receiver args : Term) (hs : (sig.rowOf op).shape = .method)
    (hr : receiver.scoped n = true)
    (ha : (if (methodArgsRow (sig.rowOf op)).shape = .tupleCall then tupleRequestReadable n args
      else if (methodArgsRow (sig.rowOf op)).request = Ty.unit then decide (args = .lit .unit)
      else args.scoped n) = true) (hcr : receiver.covers classes = true)
    (hca : args.covers classes = true) {typeArgs : List TypeScript.TypeRef}
    (hta : rowTypeArgs (sig.rowOf op) = some typeArgs) :
    readRowMethod classes sig spell n (printTerm receiver) (sig.rowOf op).spelling typeArgs
      (printMethodArgs (sig.rowOf op) args) =
      .ok (rowAnswer (sig.rowOf op) op (.app "pair" (.cons receiver (.cons args .nil)))) := by
  simp only [readRowMethod, readTerm_printTerm receiver hr hcr, ok_bind,
    readRowCall_methodArgs hl op hd args ha hca hta, Option.getD_some]
  simp only [rowAnswer, addReceiver, hs, if_true]

/-- The printed form of a row answer is the row's printed call. -/
theorem print_rowAnswer {sig : Signature Op} {n : Nat} (op : Op) (r : Term) :
    print sig n (rowAnswer (sig.rowOf op) op r) = printRow (sig.rowOf op) r := by
  simp only [rowAnswer, print_perform]

/-- The reader's two call arms agree on a row's printed head: with no declared type
arguments it is a plain `spelling(...)` call, and with them a `spelling<T…>(...)` call; both
route to `readRowCall` at the row's own type arguments (`E4-CHECK-CE-013`). -/
theorem readPerform_printRowHead {sig : Signature Op} {spell : String → List String → Option Op}
    {n : Nat} (op : Op) (args : List Expr) (answer : Except ReadRefusal (Eff Op))
    (hhead : headOf (sig.rowOf op).spelling = none)
    {typeArgs : List TypeScript.TypeRef} (hta : rowTypeArgs (sig.rowOf op) = some typeArgs)
    (hrow : readRowCall classes sig spell n (sig.rowOf op).spelling typeArgs args = some answer)
    {head : Expr} (hp : printRowHead (sig.rowOf op) = .ok head) :
    readPerform classes sig spell n (.call head args) = answer := by
  cases typeArgs with
  | nil =>
    simp only [printRowHead, hta, Except.ok.injEq] at hp
    subst head
    simp only [readPerform, hhead, hrow, Option.getD_some]
  | cons a rest =>
    simp only [printRowHead, hta, Except.ok.injEq] at hp
    subst head
    simp only [readPerform, hrow, Option.getD_some]

/-- A successfully printed readable row reads back to its row answer. -/
theorem read_printRow {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} (op : Op) (hd : sig.dom op = true) (r : Term)
    (h : requestReadable (sig.rowOf op) n r = true) (hc : r.covers classes = true)
    {x : Expr} (hp : printRow (sig.rowOf op) r = .ok x) :
    readPerform classes sig spell n x = .ok (rowAnswer (sig.rowOf op) op r) := by
  have hname : ∀ i, Var.name i ≠ (sig.rowOf op).spelling := fun i => (hl.spelling_ne_name op i).symm
  have hhead : headOf (sig.rowOf op).spelling = none := headOf_none (hl.spelling_not_reserved op)
  cases hshape : (sig.rowOf op).shape with
  | value =>
    have hr := readable_row_value hshape h
    subst r
    have htr := hl.value_trailing op hshape
    have hsp := hl.spell_row op hd
    rw [htr] at hsp
    simp only [printRow, hshape, Except.ok.injEq] at hp
    subst x
    simp [readPerform, Var.read_none hname, hhead, readRowValue, hsp, hshape]
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
      simp [readTerm_printTerm r (readable_row_request hshape hreq h) hc]
  | tupleCall =>
    simp only [requestReadable, hshape, Bool.and_eq_true] at h
    obtain ⟨typeArgs, hta⟩ := Option.isSome_iff_exists.mp h.1
    simp only [printRow, hshape, bind_eq_ok] at hp
    obtain ⟨head, hprint, hp⟩ := hp
    simp only [Except.ok.injEq] at hp
    subst x
    exact readPerform_printRowHead op _ _ hhead hta
      (readRowCall_printTupleArgs hl op hd hshape r h.2 hc hta) hprint
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
      have hm := readRowMethod_print hl op hd receiver args hshape hr ha hc.1 hc.2.1 hta
      cases typeArgs with
      | nil =>
        simp only [printRow, hshape, pairArgs?, ↓reduceIte, printMethod, hta,
          Except.ok.injEq] at hp
        subst x
        simp [readPerform, readMethod, hm]
      | cons t ts =>
        simp only [printRow, hshape, pairArgs?, ↓reduceIte, printMethod, hta,
          Except.ok.injEq] at hp
        subst x
        simp [readPerform, readMethod, hm]

/-- The tuple reading reconstructs its two arguments: a saved variable prints as its two
component reads, any other pair as the printed components. -/
theorem readTupleArgs_exact {n : Nat} {x y : Expr} {r : Term}
    (h : readTupleArgs classes n x y = .ok r) : printTupleArgs r = [x, y] := by
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
      rowTypeArgs (sig.rowOf op) = some ta ∧ printMethodArgs (sig.rowOf op) r = args := by
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
    print sig n e = .ok (match ta with
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
    (h : readMethod classes sig spell n x = .ok e) : print sig n e = .ok x := by
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
    print sig n e = .ok (rowCallImage s ta args) := by
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
    (h : readRowValue sig spell s = .ok e) : print sig n e = .ok (.ident s) := by
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

/-- The row call of `perform`: what `readPerform` accepts prints back to the tree it read. -/
theorem readPerform_exact {sig : Signature Op} {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} {x : Expr} {e : Eff Op}
    (h : readPerform classes sig spell n x = .ok e) : print sig n e = .ok x := by
  unfold readPerform at h
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

end ReadExact

end Rows

theorem name_notin (l : List String) (h : ∀ s ∈ l, s.toByteArray.data.toList.head? ≠ some 97)
    (i : Nat) : Var.name i ∉ l := fun hm => Var.name_ne (h _ hm) i rfl

theorem NativeOp.external_not_mem_all (i : Nat) : NativeOp.external i ∉ NativeOp.all := by
  simp [NativeOp.all, fnNames]

theorem NativeOp.all_complete (op : NativeOp) (h : ∀ i, op ≠ .external i) :
    op ∈ NativeOp.all := by
  cases op <;> first
    | decide
    | (rename_i f; cases f <;> decide)
    | exact (h _ rfl).elim

theorem nativeRowOf_mem_all (table : RowTable) (op : NativeOp) (h : op ∈ NativeOp.all) :
    nativeRowOf table op = op.row := by
  cases op <;> first | rfl | exact (NativeOp.external_not_mem_all _ h).elim

theorem nativeRowOf_external (table : RowTable) (i : Nat) (hi : i < table.length) :
    nativeRowOf table (.external i) = table[i] := by
  simp [nativeRowOf, List.getElem?_eq_getElem hi]

theorem lawfulTable_member (table : RowTable) (h : LawfulTable table = true)
    (row : Row) (hr : row ∈ table) :
    rowKey row ∉ NativeOp.all.map (rowKey ∘ NativeOp.row) ∧
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
  | _ => first
    | (simp only [nativeRowOf]; decide)
    | (rename_i f; cases f <;> simp only [nativeRowOf] <;> decide)

theorem nativeLawful (table : RowTable := []) (h : LawfulTable table = true := by decide) :
    LawfulSpelling (nativeSignature table) (nativeSpell table) where
  spell_row := by
    intro op hd
    cases op with
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
    | _ => first
      | rfl
      | (rename_i f; cases f <;> rfl)
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
      rw [nativeRowOf_mem_all table found hm]
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

end Effect4.Program
