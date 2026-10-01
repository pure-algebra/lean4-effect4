/-! RED CONTROL (must fail): the model with one added claim, that a decoded value fits its type
without the distinct-names premise. The instance below has field `a` twice. Expected: #guard fails. -/
/-!
# Seat EFFECT, probe 2 (2026-10-01): a model of records with name-keyed values and the codec
laws native schema support owes (note §4b), proved over the model

This is **not the tree**. It is a self-contained model in the type-algebra note's encoding B (a
mutual spine `DTy`/`DFields`, `docs/research/2026-09-18-research-type-algebra.md` §1.3), so what
is proved here is that the requirement shapes are satisfiable and exactly what they need:

* `fits_sub`: membership is monotone in width/depth/optionality subtyping **because** record
  values are name-keyed (a positional carrier fails it: the finite witness at the end);
* `decode_fits`: a decoded value fits its type;
* `encode_decode` (exactness): `decode t j = some v → encode t v = some (norm t j)`, modulo the
  named normaliser `norm` (declared keys, declared order, the first occurrence of a key);
* `decode_encode` (retraction): `encode t v = some j → decode t j = some (proj t v)`, where `proj`
  drops undeclared keys, as rc.112's struct parser does by default.

The record laws need one well-formedness premise, distinct field names (`DTy.WF`), which rc.112
enforces at construction (`vendor/effect-4.0.0-rc.112/src/SchemaAST.ts:2117-2120`).
-/

set_option autoImplicit false

namespace DataProbeEffect.RecordModel

mutual
  /-- Data types: strings, naturals and records. -/
  inductive DTy where
    | str
    | nat
    | record (fields : DFields)
  /-- A record's fields as a spine: name, whether the key may be absent, type. -/
  inductive DFields where
    | nil
    | cons (name : String) (optional : Bool) (type : DTy) (rest : DFields)
end

mutual
  /-- JSON as the wire sees it: strings, signed integers (as JSON numbers may be), objects
  with ordered entries, duplicates kept. -/
  inductive J where
    | str (s : String)
    | num (n : Int)
    | obj (entries : JEntries)
  inductive JEntries where
    | nil
    | cons (key : String) (value : J) (rest : JEntries)
end

mutual
  /-- Machine values: strings, naturals, and name-keyed records. -/
  inductive V where
    | str (s : String)
    | nat (n : Nat)
    | obj (entries : VEntries)
  inductive VEntries where
    | nil
    | cons (key : String) (value : V) (rest : VEntries)
end

deriving instance DecidableEq for DTy, DFields
deriving instance DecidableEq for J, JEntries
deriving instance DecidableEq for V, VEntries

/-! ## Lookups and names -/

/-- The first entry with key `k`. -/
def JEntries.find? (k : String) : JEntries → Option J
  | .nil => none
  | .cons key value rest => if k = key then some value else JEntries.find? k rest

/-- The first entry with key `k`. -/
def VEntries.find? (k : String) : VEntries → Option V
  | .nil => none
  | .cons key value rest => if k = key then some value else VEntries.find? k rest

/-- The first field named `k`: whether it is optional, and its type. -/
def DFields.find? (k : String) : DFields → Option (Bool × DTy)
  | .nil => none
  | .cons name optional type rest =>
      if k = name then some (optional, type) else DFields.find? k rest

def DFields.names : DFields → List String
  | .nil => []
  | .cons name _ _ rest => name :: DFields.names rest

/-! ## Well-formedness: distinct field names at every record -/

mutual
  def DTy.WF : DTy → Prop
    | .str => True
    | .nat => True
    | .record fields => DFields.WF fields ∧ (DFields.names fields).Nodup
  def DFields.WF : DFields → Prop
    | .nil => True
    | .cons _ _ type rest => DTy.WF type ∧ DFields.WF rest
end

/-! ## Membership, subtyping, the codec, the normaliser, the projection -/

mutual
  /-- `Fits`, name-keyed: every declared key is present and fits, or absent and optional;
  undeclared keys are ignored (width). -/
  def fits : DTy → V → Bool
    | .str, .str _ => true
    | .nat, .nat _ => true
    | .record fields, .obj entries => fitsFields fields entries
    | _, _ => false
  def fitsFields : DFields → VEntries → Bool
    | .nil, _ => true
    | .cons name optional type rest, entries =>
      (match VEntries.find? name entries with
        | some value => fits type value
        | none => optional) && fitsFields rest entries
end

mutual
  /-- `sub a b`, recursing on `b`: width (a may have more fields), depth (field types by `sub`),
  optionality (a required field may become optional, never the reverse), and every key of `b`
  declared by `a`. The last clause is stricter than TypeScript; see `subTS`. -/
  def sub : DTy → DTy → Bool
    | .str, .str => true
    | .nat, .nat => true
    | .record source, .record target => subFields source target
    | _, _ => false
  def subFields : DFields → DFields → Bool
    | _, .nil => true
    | source, .cons name optional type rest =>
      (match DFields.find? name source with
        | some (sourceOptional, sourceType) => sub sourceType type && (optional || !sourceOptional)
        | none => false) && subFields source rest
end

mutual
  /-- TypeScript's rule at an optional target key the source does not declare: accepted
  (`{}` is assignable to `{ x?: string }`). Kept only for the counterexample below. -/
  def subTS : DTy → DTy → Bool
    | .str, .str => true
    | .nat, .nat => true
    | .record source, .record target => subTSFields source target
    | _, _ => false
  def subTSFields : DFields → DFields → Bool
    | _, .nil => true
    | source, .cons name optional type rest =>
      (match DFields.find? name source with
        | some (sourceOptional, sourceType) => subTS sourceType type && (optional || !sourceOptional)
        | none => optional) && subTSFields source rest
end

mutual
  def decode : DTy → J → Option V
    | .str, .str s => some (.str s)
    | .nat, .num n => if 0 ≤ n then some (.nat n.toNat) else none
    | .record fields, .obj entries =>
      match decodeFields fields entries with
      | some values => some (.obj values)
      | none => none
    | _, _ => none
  def decodeFields : DFields → JEntries → Option VEntries
    | .nil, _ => some .nil
    | .cons name optional type rest, entries =>
      match JEntries.find? name entries with
      | some j =>
        match decode type j, decodeFields rest entries with
        | some v, some vs => some (.cons name v vs)
        | _, _ => none
      | none => if optional then decodeFields rest entries else none
end

mutual
  def encode : DTy → V → Option J
    | .str, .str s => some (.str s)
    | .nat, .nat n => some (.num n)
    | .record fields, .obj entries =>
      match encodeFields fields entries with
      | some js => some (.obj js)
      | none => none
    | _, _ => none
  def encodeFields : DFields → VEntries → Option JEntries
    | .nil, _ => some .nil
    | .cons name optional type rest, entries =>
      match VEntries.find? name entries with
      | some v =>
        match encode type v, encodeFields rest entries with
        | some j, some js => some (.cons name j js)
        | _, _ => none
      | none => if optional then encodeFields rest entries else none
end

mutual
  /-- The normaliser exactness is stated modulo: declared keys only, in declared order, the
  first occurrence of each. -/
  def norm : DTy → J → J
    | .str, j => j
    | .nat, j => j
    | .record fields, .obj entries => .obj (normFields fields entries)
    | .record _, j => j
  def normFields : DFields → JEntries → JEntries
    | .nil, _ => .nil
    | .cons name _ type rest, entries =>
      match JEntries.find? name entries with
      | some j => .cons name (norm type j) (normFields rest entries)
      | none => normFields rest entries
end

mutual
  /-- The projection retraction is stated modulo: what rc.112's struct parser keeps. -/
  def proj : DTy → V → V
    | .str, v => v
    | .nat, v => v
    | .record fields, .obj entries => .obj (projFields fields entries)
    | .record _, v => v
  def projFields : DFields → VEntries → VEntries
    | .nil, _ => .nil
    | .cons name _ type rest, entries =>
      match VEntries.find? name entries with
      | some v => .cons name (proj type v) (projFields rest entries)
      | none => projFields rest entries
end

/-! ## Finite sanity checks -/

def user : DTy := .record (.cons "id" false .nat (.cons "name" false .str .nil))
def wire : J := .obj (.cons "name" (.str "a") (.cons "extra" (.num 1) (.cons "id" (.num 7) .nil)))

#guard decode user wire = some (.obj (.cons "id" (.nat 7) (.cons "name" (.str "a") .nil)))
#guard (decode user wire).bind (encode user) =
  some (.obj (.cons "id" (.num 7) (.cons "name" (.str "a") .nil)))
#guard norm user wire = .obj (.cons "id" (.num 7) (.cons "name" (.str "a") .nil))
#guard decode user (.obj (.cons "name" (.str "a") .nil)) = none
#guard decode .nat (.num (-1)) = none


/-! ## Lookup lemmas -/

theorem VEntries.find?_cons_self (k : String) (v : V) (rest : VEntries) :
    VEntries.find? k (.cons k v rest) = some v := by
  show (if k = k then some v else VEntries.find? k rest) = some v
  exact if_pos rfl

theorem VEntries.find?_cons_ne {k key : String} (v : V) (rest : VEntries) (h : k ≠ key) :
    VEntries.find? k (.cons key v rest) = VEntries.find? k rest := by
  simp only [VEntries.find?, if_neg h]

theorem JEntries.find?_cons_self (k : String) (j : J) (rest : JEntries) :
    JEntries.find? k (.cons k j rest) = some j := by
  show (if k = k then some j else JEntries.find? k rest) = some j
  exact if_pos rfl

theorem JEntries.find?_cons_ne {k key : String} (j : J) (rest : JEntries) (h : k ≠ key) :
    JEntries.find? k (.cons key j rest) = JEntries.find? k rest := by
  simp only [JEntries.find?, if_neg h]

theorem DFields.not_mem_names_cons {k name : String} {o : Bool} {t : DTy} {rest : DFields}
    (h : k ∉ DFields.names (.cons name o t rest)) : k ≠ name ∧ k ∉ DFields.names rest := by
  simp only [DFields.names, List.mem_cons, not_or] at h
  exact h

/-! ## A field list never looks at a key it does not declare -/

theorem fitsFields_cons_skip : ∀ (fs : DFields) (k : String) (v : V) (vs : VEntries),
    k ∉ DFields.names fs → fitsFields fs (.cons k v vs) = fitsFields fs vs
  | .nil, _, _, _, _ => rfl
  | .cons name _ _ rest, k, v, vs, h => by
    have ⟨hne, hrest⟩ := DFields.not_mem_names_cons h
    have hne' : name ≠ k := fun e => hne e.symm
    simp only [fitsFields, VEntries.find?_cons_ne v vs hne', fitsFields_cons_skip rest k v vs hrest]

theorem encodeFields_cons_skip : ∀ (fs : DFields) (k : String) (v : V) (vs : VEntries),
    k ∉ DFields.names fs → encodeFields fs (.cons k v vs) = encodeFields fs vs
  | .nil, _, _, _, _ => rfl
  | .cons name _ _ rest, k, v, vs, h => by
    have ⟨hne, hrest⟩ := DFields.not_mem_names_cons h
    have hne' : name ≠ k := fun e => hne e.symm
    simp only [encodeFields, VEntries.find?_cons_ne v vs hne', encodeFields_cons_skip rest k v vs hrest]

theorem decodeFields_cons_skip : ∀ (fs : DFields) (k : String) (j : J) (es : JEntries),
    k ∉ DFields.names fs → decodeFields fs (.cons k j es) = decodeFields fs es
  | .nil, _, _, _, _ => rfl
  | .cons name _ _ rest, k, j, es, h => by
    have ⟨hne, hrest⟩ := DFields.not_mem_names_cons h
    have hne' : name ≠ k := fun e => hne e.symm
    simp only [decodeFields, JEntries.find?_cons_ne j es hne', decodeFields_cons_skip rest k j es hrest]

/-! ## The codec emits only declared keys -/

theorem decodeFields_find_none : ∀ (fs : DFields) (es : JEntries) (vs : VEntries) (k : String),
    decodeFields fs es = some vs → k ∉ DFields.names fs → VEntries.find? k vs = none
  | .nil, _, vs, _, h, _ => by
    simp only [decodeFields, Option.some.injEq] at h
    subst h
    rfl
  | .cons name o t rest, es, vs, k, h, hk => by
    have ⟨hne, hrest⟩ := DFields.not_mem_names_cons hk
    cases hf : JEntries.find? name es with
    | some j =>
      cases hdj : decode t j with
      | none => simp only [decodeFields, hf, hdj, reduceCtorEq] at h
      | some v =>
        cases hdr : decodeFields rest es with
        | none => simp only [decodeFields, hf, hdj, hdr, reduceCtorEq] at h
        | some vs' =>
          simp only [decodeFields, hf, hdj, hdr, Option.some.injEq] at h
          subst h
          rw [VEntries.find?_cons_ne v vs' hne]
          exact decodeFields_find_none rest es vs' k hdr hrest
    | none =>
      cases o with
      | false => simp only [decodeFields, hf, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
      | true =>
        simp only [decodeFields, hf, ↓reduceIte] at h
        exact decodeFields_find_none rest es vs k h hrest

theorem encodeFields_find_none : ∀ (fs : DFields) (vs : VEntries) (js : JEntries) (k : String),
    encodeFields fs vs = some js → k ∉ DFields.names fs → JEntries.find? k js = none
  | .nil, _, js, _, h, _ => by
    simp only [encodeFields, Option.some.injEq] at h
    subst h
    rfl
  | .cons name o t rest, vs, js, k, h, hk => by
    have ⟨hne, hrest⟩ := DFields.not_mem_names_cons hk
    cases hf : VEntries.find? name vs with
    | some v =>
      cases hej : encode t v with
      | none => simp only [encodeFields, hf, hej, reduceCtorEq] at h
      | some j =>
        cases her : encodeFields rest vs with
        | none => simp only [encodeFields, hf, hej, her, reduceCtorEq] at h
        | some js' =>
          simp only [encodeFields, hf, hej, her, Option.some.injEq] at h
          subst h
          rw [JEntries.find?_cons_ne j js' hne]
          exact encodeFields_find_none rest vs js' k her hrest
    | none =>
      cases o with
      | false => simp only [encodeFields, hf, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
      | true =>
        simp only [encodeFields, hf, ↓reduceIte] at h
        exact encodeFields_find_none rest vs js k h hrest


theorem DFields.find?_cons_self (k : String) (o : Bool) (t : DTy) (rest : DFields) :
    DFields.find? k (.cons k o t rest) = some (o, t) := by
  show (if k = k then some (o, t) else DFields.find? k rest) = some (o, t)
  exact if_pos rfl

theorem DFields.find?_cons_ne {k name : String} (o : Bool) (t : DTy) (rest : DFields)
    (h : k ≠ name) : DFields.find? k (.cons name o t rest) = DFields.find? k rest := by
  simp only [DFields.find?, if_neg h]

/-! ## S-b2: a decoded value fits its type -/

mutual
theorem decode_fits : ∀ (t : DTy) (j : J) (v : V), DTy.WF t → decode t j = some v →
    fits t v = true
  | .str, .str s, v, _, h => by
    simp only [decode, Option.some.injEq] at h
    subst h
    rfl
  | .str, .num _, _, _, h => by simp only [decode, reduceCtorEq] at h
  | .str, .obj _, _, _, h => by simp only [decode, reduceCtorEq] at h
  | .nat, .num n, v, _, h => by
    simp only [decode] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      rfl
    · simp only [reduceCtorEq] at h
  | .nat, .str _, _, _, h => by simp only [decode, reduceCtorEq] at h
  | .nat, .obj _, _, _, h => by simp only [decode, reduceCtorEq] at h
  | .record fs, .obj es, v, hwf, h => by
    simp only [DTy.WF] at hwf
    cases hd : decodeFields fs es with
    | none => simp only [decode, hd, reduceCtorEq] at h
    | some vs =>
      simp only [decode, hd, Option.some.injEq] at h
      subst h
      simp only [fits]
      exact decodeFields_fits fs es vs hwf hd
  | .record _, .str _, _, _, h => by simp only [decode, reduceCtorEq] at h
  | .record _, .num _, _, _, h => by simp only [decode, reduceCtorEq] at h
theorem decodeFields_fits : ∀ (fs : DFields) (es : JEntries) (vs : VEntries),
    DFields.WF fs ∧ (DFields.names fs).Nodup → decodeFields fs es = some vs →
    fitsFields fs vs = true
  | .nil, _, _, _, _ => rfl
  | .cons name o t rest, es, vs, hwf, h => by
    simp only [DFields.WF, DFields.names, List.nodup_cons] at hwf
    obtain ⟨⟨htwf, hrwf⟩, hnotin, hnd⟩ := hwf
    cases hf : JEntries.find? name es with
    | some j =>
      cases hdj : decode t j with
      | none => simp only [decodeFields, hf, hdj, reduceCtorEq] at h
      | some v =>
        cases hdr : decodeFields rest es with
        | none => simp only [decodeFields, hf, hdj, hdr, reduceCtorEq] at h
        | some vs' =>
          simp only [decodeFields, hf, hdj, hdr, Option.some.injEq] at h
          subst h
          simp only [fitsFields, VEntries.find?_cons_self, fitsFields_cons_skip rest name v vs' hnotin,
            decode_fits t j v htwf hdj, decodeFields_fits rest es vs' ⟨hrwf, hnd⟩ hdr, Bool.and_self]
    | none =>
      cases o with
      | false => simp only [decodeFields, hf, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
      | true =>
        simp only [decodeFields, hf, ↓reduceIte] at h
        simp only [fitsFields, decodeFields_find_none rest es vs name h hnotin,
          decodeFields_fits rest es vs ⟨hrwf, hnd⟩ h, Bool.and_self]
end

/-! ## S-b1, exactness: what decodes re-encodes to the input, modulo the normaliser -/

mutual
theorem encode_decode : ∀ (t : DTy) (j : J) (v : V), DTy.WF t → decode t j = some v →
    encode t v = some (norm t j)
  | .str, .str s, v, _, h => by
    simp only [decode, Option.some.injEq] at h
    subst h
    rfl
  | .str, .num _, _, _, h => by simp only [decode, reduceCtorEq] at h
  | .str, .obj _, _, _, h => by simp only [decode, reduceCtorEq] at h
  | .nat, .num n, v, _, h => by
    simp only [decode] at h
    split at h
    · rename_i hn
      simp only [Option.some.injEq] at h
      subst h
      simp only [encode, norm, Option.some.injEq, J.num.injEq]
      exact Int.toNat_of_nonneg hn
    · simp only [reduceCtorEq] at h
  | .nat, .str _, _, _, h => by simp only [decode, reduceCtorEq] at h
  | .nat, .obj _, _, _, h => by simp only [decode, reduceCtorEq] at h
  | .record fs, .obj es, v, hwf, h => by
    simp only [DTy.WF] at hwf
    cases hd : decodeFields fs es with
    | none => simp only [decode, hd, reduceCtorEq] at h
    | some vs =>
      simp only [decode, hd, Option.some.injEq] at h
      subst h
      simp only [encode, norm, encodeFields_decodeFields fs es vs hwf hd]
  | .record _, .str _, _, _, h => by simp only [decode, reduceCtorEq] at h
  | .record _, .num _, _, _, h => by simp only [decode, reduceCtorEq] at h
theorem encodeFields_decodeFields : ∀ (fs : DFields) (es : JEntries) (vs : VEntries),
    DFields.WF fs ∧ (DFields.names fs).Nodup → decodeFields fs es = some vs →
    encodeFields fs vs = some (normFields fs es)
  | .nil, _, vs, _, h => by
    simp only [decodeFields, Option.some.injEq] at h
    subst h
    rfl
  | .cons name o t rest, es, vs, hwf, h => by
    simp only [DFields.WF, DFields.names, List.nodup_cons] at hwf
    obtain ⟨⟨htwf, hrwf⟩, hnotin, hnd⟩ := hwf
    cases hf : JEntries.find? name es with
    | some j =>
      cases hdj : decode t j with
      | none => simp only [decodeFields, hf, hdj, reduceCtorEq] at h
      | some v =>
        cases hdr : decodeFields rest es with
        | none => simp only [decodeFields, hf, hdj, hdr, reduceCtorEq] at h
        | some vs' =>
          simp only [decodeFields, hf, hdj, hdr, Option.some.injEq] at h
          subst h
          simp only [encodeFields, VEntries.find?_cons_self, encode_decode t j v htwf hdj,
            encodeFields_cons_skip rest name v vs' hnotin,
            encodeFields_decodeFields rest es vs' ⟨hrwf, hnd⟩ hdr, normFields, hf]
    | none =>
      cases o with
      | false => simp only [decodeFields, hf, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
      | true =>
        simp only [decodeFields, hf, ↓reduceIte] at h
        simp only [encodeFields, decodeFields_find_none rest es vs name h hnotin, ↓reduceIte,
          encodeFields_decodeFields rest es vs ⟨hrwf, hnd⟩ h, normFields, hf]
end

/-! ## S-b1, retraction: what encodes decodes back, modulo the projection -/

mutual
theorem decode_encode : ∀ (t : DTy) (v : V) (j : J), DTy.WF t → encode t v = some j →
    decode t j = some (proj t v)
  | .str, .str s, j, _, h => by
    simp only [encode, Option.some.injEq] at h
    subst h
    rfl
  | .str, .nat _, _, _, h => by simp only [encode, reduceCtorEq] at h
  | .str, .obj _, _, _, h => by simp only [encode, reduceCtorEq] at h
  | .nat, .nat n, j, _, h => by
    simp only [encode, Option.some.injEq] at h
    subst h
    simp only [decode, proj, Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast]
  | .nat, .str _, _, _, h => by simp only [encode, reduceCtorEq] at h
  | .nat, .obj _, _, _, h => by simp only [encode, reduceCtorEq] at h
  | .record fs, .obj vs, j, hwf, h => by
    simp only [DTy.WF] at hwf
    cases he : encodeFields fs vs with
    | none => simp only [encode, he, reduceCtorEq] at h
    | some js =>
      simp only [encode, he, Option.some.injEq] at h
      subst h
      simp only [decode, proj, decodeFields_encodeFields fs vs js hwf he]
  | .record _, .str _, _, _, h => by simp only [encode, reduceCtorEq] at h
  | .record _, .nat _, _, _, h => by simp only [encode, reduceCtorEq] at h
theorem decodeFields_encodeFields : ∀ (fs : DFields) (vs : VEntries) (js : JEntries),
    DFields.WF fs ∧ (DFields.names fs).Nodup → encodeFields fs vs = some js →
    decodeFields fs js = some (projFields fs vs)
  | .nil, _, js, _, h => by
    simp only [encodeFields, Option.some.injEq] at h
    subst h
    rfl
  | .cons name o t rest, vs, js, hwf, h => by
    simp only [DFields.WF, DFields.names, List.nodup_cons] at hwf
    obtain ⟨⟨htwf, hrwf⟩, hnotin, hnd⟩ := hwf
    cases hf : VEntries.find? name vs with
    | some v =>
      cases hej : encode t v with
      | none => simp only [encodeFields, hf, hej, reduceCtorEq] at h
      | some j =>
        cases her : encodeFields rest vs with
        | none => simp only [encodeFields, hf, hej, her, reduceCtorEq] at h
        | some js' =>
          simp only [encodeFields, hf, hej, her, Option.some.injEq] at h
          subst h
          simp only [decodeFields, JEntries.find?_cons_self, decode_encode t v j htwf hej,
            decodeFields_cons_skip rest name j js' hnotin,
            decodeFields_encodeFields rest vs js' ⟨hrwf, hnd⟩ her, projFields, hf]
    | none =>
      cases o with
      | false => simp only [encodeFields, hf, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h
      | true =>
        simp only [encodeFields, hf, ↓reduceIte] at h
        simp only [decodeFields, encodeFields_find_none rest vs js name h hnotin, ↓reduceIte,
          decodeFields_encodeFields rest vs js ⟨hrwf, hnd⟩ h, projFields, hf]
end

/-! ## S-a/R3's `Fits` clause: membership is monotone in `sub` (name-keyed values) -/

theorem fitsFields_find : ∀ (fs : DFields) (vs : VEntries) (k : String) (o : Bool) (t : DTy),
    fitsFields fs vs = true → DFields.find? k fs = some (o, t) →
    (match VEntries.find? k vs with
      | some v => fits t v
      | none => o) = true
  | .nil, _, _, _, _, _, h => by simp only [DFields.find?, reduceCtorEq] at h
  | .cons name o' t' rest, vs, k, o, t, hf, h => by
    simp only [fitsFields, Bool.and_eq_true] at hf
    by_cases hk : k = name
    · subst hk
      rw [DFields.find?_cons_self, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hf.1
    · rw [DFields.find?_cons_ne o' t' rest hk] at h
      exact fitsFields_find rest vs k o t hf.2 h

mutual
theorem fits_sub : ∀ (b a : DTy) (v : V), fits a v = true → sub a b = true → fits b v = true
  | .str, .str, _, hf, _ => hf
  | .str, .nat, _, _, hs => by simp only [sub, Bool.false_eq_true] at hs
  | .str, .record _, _, _, hs => by simp only [sub, Bool.false_eq_true] at hs
  | .nat, .nat, _, hf, _ => hf
  | .nat, .str, _, _, hs => by simp only [sub, Bool.false_eq_true] at hs
  | .nat, .record _, _, _, hs => by simp only [sub, Bool.false_eq_true] at hs
  | .record gs, .record fs, v, hf, hs => by
    cases v with
    | obj vs =>
      simp only [fits] at hf ⊢
      simp only [sub] at hs
      exact fitsFields_sub gs fs vs hf hs
    | str _ => simp only [fits, Bool.false_eq_true] at hf
    | nat _ => simp only [fits, Bool.false_eq_true] at hf
  | .record _, .str, _, _, hs => by simp only [sub, Bool.false_eq_true] at hs
  | .record _, .nat, _, _, hs => by simp only [sub, Bool.false_eq_true] at hs
theorem fitsFields_sub : ∀ (gs fs : DFields) (vs : VEntries), fitsFields fs vs = true →
    subFields fs gs = true → fitsFields gs vs = true
  | .nil, _, _, _, _ => rfl
  | .cons name o t rest, fs, vs, hf, hs => by
    simp only [subFields, Bool.and_eq_true] at hs
    obtain ⟨hhead, hrest⟩ := hs
    simp only [fitsFields, Bool.and_eq_true]
    refine ⟨?_, fitsFields_sub rest fs vs hf hrest⟩
    cases hfind : DFields.find? name fs with
    | none => simp only [hfind, Bool.false_eq_true] at hhead
    | some p =>
      obtain ⟨o', t'⟩ := p
      simp only [hfind, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hhead
      obtain ⟨hsub, hopt⟩ := hhead
      have hv := fitsFields_find fs vs name o' t' hf hfind
      cases hvf : VEntries.find? name vs with
      | some v =>
        simp only [hvf] at hv ⊢
        exact fits_sub t t' v hv hsub
      | none =>
        simp only [hvf] at hv ⊢
        cases hopt with
        | inl h => exact h
        | inr h =>
          rw [hv] at h
          exact absurd h (by decide)
end

/-! ## Finite witnesses: what breaks monotonicity -/

/-- TypeScript's rule at an undeclared optional key (`subTS`): `{}` is assignable to
`{ x?: string }`, and a value carrying `x: 1` fits the first and not the second. -/
def emptyRec : DTy := .record .nil
def optX : DTy := .record (.cons "x" true .str .nil)
def valueX : V := .obj (.cons "x" (.nat 1) .nil)

#guard fits emptyRec valueX = true
#guard subTS emptyRec optX = true
#guard fits optX valueX = false
#guard sub emptyRec optX = false

/-- A positional carrier (values by position, names only in the type) fails width
subsumption even for the sound `sub`: the value of `{a, b}` does not fit `{a}`. -/
def posFitsFields : DFields → List V → Bool
  | .nil, [] => true
  | .cons _ _ t rest, v :: vs => fits t v && posFitsFields rest vs
  | _, _ => false

def abFields : DFields := .cons "a" false .str (.cons "b" false .nat .nil)
def aFields : DFields := .cons "a" false .str .nil

#guard sub (.record abFields) (.record aFields) = true
#guard posFitsFields abFields [.str "x", .nat 1] = true
#guard posFitsFields aFields [.str "x", .nat 1] = false
#guard fits (.record aFields) (.obj (.cons "a" (.str "x") (.cons "b" (.nat 1) .nil))) = true

/-! ## Axioms -/


def dupA : DTy := .record (.cons "a" false (.record .nil) (.cons "a" false (.record (.cons "x" false .str .nil)) .nil))
def dupWire : J := .obj (.cons "a" (.obj (.cons "x" (.str "s") .nil)) .nil)
#guard (decode dupA dupWire).isSome
#guard (decode dupA dupWire).all (fits dupA)

end DataProbeEffect.RecordModel
