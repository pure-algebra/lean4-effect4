import Effect4.Codegen.Metadata
import Effect4.Laws.Auto.Inversion

/-!
# Retraction and exactness of structural type metadata

Concept: Exact Codecs & Data Plane Embeddings. Proposed registry claim: `type-metadata-exact`.
Role: exact embedding. Consumer: the record term printer and reader, serving R2 and R3.
Reach: every raw `Ty` and structural target expression, without formation or `Val.WF` premises.
Limits: these laws do not establish rendered-source parsing or target execution agreement.
The brief is `docs/research/2026-10-03-data-language/metadata-brief.md`.
-/

set_option autoImplicit false

namespace Effect4.Codegen.Metadata
open Effect4.Store TypeScript

theorem readByte_writeByte (b : UInt8) : readByte (writeByte b) = some b := by
  simp only [writeByte, readByte]
  rw [if_pos (UInt8.toNat_lt b), UInt8.ofNat_toNat]

theorem readByteList_writeByteList (bs : Bytes) :
    (bs.map writeByte).mapM readByte = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, List.mapM_cons, readByte_writeByte, ih,
      Option.bind_eq_bind, Option.bind_some]
    rfl

theorem readBytes_writeBytes (bs : Bytes) : readBytes (writeBytes bs) = some bs :=
  readByteList_writeByteList bs

theorem readNat_writeNat (n : Nat) : readNat (writeNat n) = some n := by
  simp only [writeNat, readNat, readBytes_writeBytes, Option.bind_eq_bind, Option.bind_some]
  rw [if_neg (natBytes_head n), natOfDigits_natBytes]

theorem readBits_writeNat (bits : UInt64) : readBits (writeNat bits.toNat) = some bits := by
  simp only [readBits, readNat_writeNat, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos (UInt64.toNat_lt bits), UInt64.ofNat_toNat]

theorem readByte_exact (e : Expr) (b : UInt8) (h : readByte e = some b) :
    writeByte b = e := by
  unfold readByte at h
  split at h
  · next n =>
    split at h
    · next hn =>
      cases h
      simp only [writeByte, UInt8.toNat_ofNat_of_lt' hn]
    · exact nomatch h
  · exact nomatch h

theorem readByteList_exact : ∀ (es : List Expr) (bs : Bytes),
    es.mapM readByte = some bs → bs.map writeByte = es
  | [], _, h => by
    cases h
    rfl
  | e :: es, _, h => by
    simp only [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨bs, hbs, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    simp only [List.map_cons, readByte_exact e b hb, readByteList_exact es bs hbs]

theorem readBytes_exact (e : Expr) (bs : Bytes) (h : readBytes e = some bs) :
    writeBytes bs = e := by
  unfold readBytes at h
  split at h
  · next es => exact congrArg Expr.arr (readByteList_exact es bs h)
  · exact nomatch h

theorem readNat_exact (e : Expr) (n : Nat) (h : readNat e = some n) : writeNat n = e := by
  unfold readNat at h
  obtain ⟨bs, hbs, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · exact nomatch h
  · next hn =>
    cases h
    unfold writeNat
    rw [natBytes_natOfDigits bs hn]
    exact readBytes_exact e bs hbs

theorem readBits_exact (e : Expr) (bits : UInt64) (h : readBits e = some bits) :
    writeNat bits.toNat = e := by
  unfold readBits at h
  obtain ⟨n, hn, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · next hlt =>
    cases h
    rw [UInt64.toNat_ofNat_of_lt' hlt]
    exact readNat_exact e n hn
  · exact nomatch h

/-- The list companion uses the children's retraction hypotheses. -/
theorem readValues_map_write (vs : List Val)
    (h : ∀ v ∈ vs, readValue (writeValue v) = some v) :
    readValues (vs.map writeValue) = some vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have hv := h v List.mem_cons_self
    have hs := ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
    simp only [List.map_cons, readValues, hv, hs, Option.bind_eq_bind, Option.bind_some]

/-- Reading the generated value fold needs no frame-size bound. -/
theorem readValue_writeValue (v : Val) : readValue (writeValue v) = some v := by
  induction v using Val.ind with
  | unit => rfl
  | bool b => rfl
  | nat n =>
    change (readNat (writeNat n)).map Val.nat = some (.nat n)
    rw [readNat_writeNat]
    rfl
  | str s => rfl
  | bytes bs =>
    change (readBytes (writeBytes bs)).map Val.bytes = some (.bytes bs)
    rw [readBytes_writeBytes]
    rfl
  | list vs ih =>
    simp only [writeValue, cata_val, cata_pos_list_val_eq, valueAlgebra]
    change (readValues (vs.map writeValue)).map Val.list = some (.list vs)
    rw [readValues_map_write vs ih]
    rfl
  | pair a b ha hb =>
    change (do
      let a' ← readValue (writeValue a)
      let b' ← readValue (writeValue b)
      some (Val.pair a' b')) = some (.pair a b)
    simp only [ha, hb, Option.bind_eq_bind, Option.bind_some]
  | none => rfl
  | some a ha =>
    change (readValue (writeValue a)).map Val.some = some (.some a)
    rw [ha]
    rfl
  | ctor i vs ih =>
    simp only [writeValue, cata_val, cata_pos_list_val_eq, valueAlgebra]
    change (do
      let i' ← readNat (writeNat i)
      let vs' ← readValues (vs.map writeValue)
      some (Val.ctor i' vs')) = some (.ctor i vs)
    simp only [readNat_writeNat, readValues_map_write vs ih, Option.bind_eq_bind,
      Option.bind_some]
  | ref k bs =>
    change (do
      let k' ← readByte (writeByte k)
      let bs' ← readBytes (writeBytes bs)
      some (Val.ref k' bs')) = some (.ref k bs)
    simp only [readByte_writeByte, readBytes_writeBytes, Option.bind_eq_bind, Option.bind_some]
  | handle k n =>
    change (do
      let k' ← readByte (writeByte k)
      let n' ← readNat (writeNat n)
      some (Val.handle k' n')) = some (.handle k n)
    simp only [readByte_writeByte, readNat_writeNat, Option.bind_eq_bind, Option.bind_some]
  | negInt n =>
    change (readNat (writeNat n)).map Val.negInt = some (.negInt n)
    rw [readNat_writeNat]
    rfl
  | float bits =>
    change (readBits (writeNat bits.toNat)).map Val.float = some (.float bits)
    rw [readBits_writeNat]
    rfl

mutual
  /-- Every accepted value expression is precisely the generated fold's image. -/
  theorem readValue_exact (e : Expr) (v : Val) (h : readValue e = some v) :
      writeValue v = e := by
    unfold readValue at h
    split at h
    · cases h; rfl
    · cases h; rfl
    · next n =>
      obtain ⟨n', hn, hv⟩ := Option.map_eq_some_iff.mp h
      cases hv
      exact congrArg (fun x => Expr.arr [.int 2, x]) (readNat_exact n n' hn)
    · cases h; rfl
    · next bs =>
      obtain ⟨bs', hbs, hv⟩ := Option.map_eq_some_iff.mp h
      cases hv
      exact congrArg (fun x => Expr.arr [.int 8, x]) (readBytes_exact bs bs' hbs)
    · next es =>
      obtain ⟨vs, hvs, hv⟩ := Option.map_eq_some_iff.mp h
      cases hv
      simp only [writeValue, cata_val, cata_pos_list_val_eq, valueAlgebra]
      exact congrArg (fun xs => Expr.arr [.int 4, .arr xs]) (readValues_exact es vs hvs)
    · next a b =>
      obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨b', hb, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      change Expr.arr [.int 5, writeValue a', writeValue b'] = _
      rw [readValue_exact a a' ha, readValue_exact b b' hb]
    · cases h; rfl
    · next a =>
      obtain ⟨a', ha, hv⟩ := Option.map_eq_some_iff.mp h
      cases hv
      exact congrArg (fun x => Expr.arr [.int 7, x]) (readValue_exact a a' ha)
    · next i es =>
      obtain ⟨i', hi, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨vs, hvs, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      simp only [writeValue, cata_val, cata_pos_list_val_eq, valueAlgebra]
      change Expr.arr [.int 10, writeNat i', .arr (vs.map writeValue)] = _
      rw [readNat_exact i i' hi, readValues_exact es vs hvs]
    · next k bs =>
      obtain ⟨k', hk, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨bs', hbs, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      change Expr.arr [.int 11, writeByte k', writeBytes bs'] = _
      rw [readByte_exact k k' hk, readBytes_exact bs bs' hbs]
    · next k n =>
      obtain ⟨k', hk, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨n', hn, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      change Expr.arr [.int 12, writeByte k', writeNat n'] = _
      rw [readByte_exact k k' hk, readNat_exact n n' hn]
    · next n =>
      obtain ⟨n', hn, hv⟩ := Option.map_eq_some_iff.mp h
      cases hv
      exact congrArg (fun x => Expr.arr [.int 13, x]) (readNat_exact n n' hn)
    · next n =>
      obtain ⟨bits, hb, hv⟩ := Option.map_eq_some_iff.mp h
      cases hv
      exact congrArg (fun x => Expr.arr [.int 14, x]) (readBits_exact n bits hb)
    · exact nomatch h
  termination_by sizeOf e
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

  /-- The exact image retains recursive child order. -/
  theorem readValues_exact (es : List Expr) (vs : List Val) (h : readValues es = some vs) :
      vs.map writeValue = es := by
    cases es with
    | nil => cases h; rfl
    | cons e es =>
      simp only [readValues] at h
      obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨vs, hvs, h⟩ := Option.bind_eq_some_iff.mp h
      cases h
      simp only [List.map_cons, readValue_exact e v hv, readValues_exact es vs hvs]
  termination_by sizeOf es
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega
end

/-- Every raw type declaration reads back, without normalization or frame-size premises.
Proposed claim `type-metadata-exact`, serving the record reader under R2 and R3. -/
theorem readTy_writeTy (t : Effect4.Program.Ty) : readTy (writeTy t) = some t := by
  simp only [readTy, writeTy, readValue_writeValue, Option.bind_some, Canonical.ofVal_toVal]

/-- Every accepted metadata expression is the exact image of its raw type declaration.
This is structural syntax equality, not a target execution theorem. -/
theorem readTy_exact (e : Expr) (t : Effect4.Program.Ty) (h : readTy e = some t) :
    writeTy t = e := by
  unfold readTy at h
  obtain ⟨v, hv, ht⟩ := Option.bind_eq_some_iff.mp h
  have he := readValue_exact e v hv
  rw [Canonical.ofVal_exact ht] at he
  exact he

/-- The two directions of the proposed `type-metadata-exact` claim, with no source restriction. -/
theorem type_metadata_exact :
    (∀ t : Effect4.Program.Ty, readTy (writeTy t) = some t) ∧
    (∀ (e : Expr) (t : Effect4.Program.Ty), readTy e = some t → writeTy t = e) :=
  ⟨readTy_writeTy, readTy_exact⟩

end Effect4.Codegen.Metadata
