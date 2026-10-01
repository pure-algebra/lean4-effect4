import P4Algebra
import Effect4.Program.Typed

/-!
# Seat P: the executable value check on the copy, records named (type-language probe, 2026-10-01)

Research probe. A copy of `Val.hasTy` (`src/Effect4/Program/Typed.lean:34-101` at `bff50631`)
over `ProbeP.Ty`, with the arms the wave appends, and its laws: `hasTy_sub` (membership respects
`sub`), `hasTy_normalize` (R3.2, no premise), the join laws, the named incompleteness
`record_sub_not_complete` (TY-10), and the leaf table's membership obligation (one lemma per
edge, `hasTy_leafEdge`).

**The record arm, named (row 165 (a), ruled 2026-10-01).** A record value is
`ctor 0 [list names, list values]` (`recordParts?`): the present fields' names, as `Val.str`, and
their values, both in canonical order. The arm builds one checker per written field (`checkers`,
the field-list companion of the structural recursion), sorts the *checkers* with the
payload-polymorphic `canonF`, and reads the value against them by a merge (`namedHasTy`): a name
equal to the next canonical field's is read at that field's type; a canonical field the value does
not name must be optional, and is absent from both lists (question 4a); any other name (one the
type does not have, a repeat, one out of canonical order) fails. The recursion never sorts types,
so it stays structural. The positional arm this replaces (`fieldsHasTy` over `ctor 0 [v₁ … vₙ]`,
an optional slot wrapped in `none`/`some`) is at commit `1b069d15`; the cost of each is in
`note.md`.

**The map arm**: a map value is `list [pair k₁ v₁, …]` (the store's image of an association list,
`Image.list (Image.pair …)`), keys strictly ascending in the admitted key order (`keyLt`: strings
by UTF-8 bytes, naturals numerically), every key a member of the key type, every value of the
value type.

**T's arms.** `tuple`: a list value read item by item (arity two is `prod`'s value, so normalizing
`tuple [a, b]` to `prod a b` keeps membership, `hasTy_tuple_pair`); `app n args`: opaque, the
handle arm at target `n` (`handleHasTy`, production's `.handle` arm extracted so both share it;
the arguments are not read, which invariance makes monotone, and `app n []` is `handle n`);
`null`: `Val.none`; `undefined`: `Val.unit` (below `void`, one image); `int`: `nat n` for `n ≥ 0`
and `ctor 1 [nat k]` for `-(k+1)`; `number`: an integer's image or `ctor 2 [bytes b]` with eight
bytes (binary64); `bytes`: `Val.bytes`. The leaf images are stand-ins (assumed: their encodings
are T's rows), chosen so every edge of the leaf table is a membership inclusion; Lean's generated
`Int` image (`ctor 0 [nat n]`) is not one (`generated_int_image_breaks_tower`).
-/

set_option autoImplicit false

namespace ProbeP

open Effect4.Machine
open ProbeP.Field ProbeP.Ty

/-- Every typed failure of a cause has an image satisfying `member` (`causeAdmits`'s shape,
`Program/ErrorImage.lean:44`, with the type argument dropped: it is not read). -/
def causeAdmitsP (member : Val → Bool) (c : CauseV) : Bool :=
  c.reasons.all fun r =>
    match r with
    | .fail e _ =>
      match Effect4.Program.valOfErr e with
      | some v => member v
      | none => false
    | .die _ _ | .interrupt _ _ => true

theorem causeAdmitsP_mono {f g : Val → Bool} (h : ∀ w, f w = true → g w = true) (c : CauseV)
    (hc : causeAdmitsP f c = true) : causeAdmitsP g c = true := by
  unfold causeAdmitsP at hc ⊢
  rw [List.all_eq_true] at hc ⊢
  intro r hr
  have hrc := hc r hr
  match r, hrc with
  | .fail e ann, hrc =>
    show (match Effect4.Program.valOfErr e with | some v => g v | none => false) = true
    revert hrc
    show (match Effect4.Program.valOfErr e with | some v => f v | none => false) = true → _
    cases Effect4.Program.valOfErr e with
    | none => intro hrc; exact hrc
    | some w => intro hrc; exact h w hrc
  | .die _ _, _ => rfl
  | .interrupt _ _, _ => rfl

/-- A record value's parts: its names and its values (row 165 (a): `ctor 0 [list names, list
values]`, no new `Val` frame). -/
def recordParts? : Val → Option (List Val × List Val)
  | .ctor 0 [.list ns, .list xs] => some (ns, xs)
  | _ => none

/-- **The named read**: the canonical checkers against the value's names and values. A name equal
to the next field's is read at its type; a field the value does not name must be optional (absent
from both lists); anything else fails. -/
def namedHasTy : List (String × Bool × (Val → Bool)) → List Val → List Val → Bool
  | [], [], [] => true
  | (_, o, _) :: cs, [], [] => o && namedHasTy cs [] []
  | (n, o, c) :: cs, .str m :: ns, x :: xs =>
    if m = n then c x && namedHasTy cs ns xs
    else o && namedHasTy cs (.str m :: ns) (x :: xs)
  | _, _, _ => false

/-- A tuple's items, one for one. -/
def itemsHasTy : List (Val → Bool) → List Val → Bool
  | [], [] => true
  | c :: cs, x :: xs => c x && itemsHasTy cs xs
  | _, _ => false

/-- The admitted map-key order: strings by UTF-8 bytes, naturals numerically. -/
def keyLt : Val → Val → Bool
  | .str a, .str b => Effect4.Program.Ty.ltKey (bytesKey a) (bytesKey b)
  | .nat m, .nat n => decide (m < n)
  | _, _ => false

/-- The entries of a map value: pairs, keys strictly ascending. -/
def sortedEntries : List Val → Bool
  | [] => true
  | [.pair _ _] => true
  | .pair a _ :: .pair b y :: rest => keyLt a b && sortedEntries (.pair b y :: rest)
  | _ => false

/-- Every entry is a pair whose key and value pass their checks. -/
def entriesHasTy (ck cv : Val → Bool) (es : List Val) : Bool :=
  sortedEntries es && es.all fun e =>
    match e with
    | .pair a x => ck a && cv x
    | _ => false

/-- Production's `.handle` arm, extracted so that `app` shares it (copied text). -/
def handleHasTy (target : String) (v : Val) (allocated : List String) : Bool :=
  match v with
  | .handle kind index =>
    match HandleKind.ofByte? kind with
    | some .cell => target == Effect4.Program.NativeOp.refTarget
    | some .promise => target == Effect4.Program.NativeOp.deferredTarget
    | some .scope => target == Effect4.Program.Ty.scopeTarget
    | some .external =>
      Effect4.Program.externalHandleTarget target && allocated[index]? == some target
    | _ => false
  | _ => target == Effect4.Program.Ty.contextTarget && (Val.context? v).isSome

/-- An integer's image (assumed stand-in): a natural for `n ≥ 0`, `ctor 1 [nat k]` for `-(k+1)`.
The non-negative half is `nat`'s own image, which is what makes `nat ⊑ int` a membership
inclusion. -/
def intImage : Val → Bool
  | .nat _ => true
  | .ctor 1 [.nat _] => true
  | _ => false

/-- A binary64 number's image (assumed stand-in): an integer's, or eight IEEE bytes. -/
def numberImage (v : Val) : Bool :=
  intImage v || match v with
    | .ctor 2 [.bytes bs] => decide (bs.length = 8)
    | _ => false

mutual
/-- `Val.hasTy`, copied, with the wave's arms. -/
def hasTy (v : Val) (ty : Ty) (allocated : List String) : Bool :=
  match ty with
  | .unit => match v with | .unit => true | _ => false
  | .nat => match v with | .nat _ => true | _ => false
  | .bool => match v with | .bool _ => true | _ => false
  | .string => match v with | .str _ => true | _ => false
  | .option inner =>
    match v with
    | .none => true
    | .some x => hasTy x inner allocated
    | _ => false
  | .handle target => handleHasTy target v allocated
  | .fiberOf _ _ => match v with | Value.fiber _ => true | _ => false
  | .refOf _ =>
    match v with
    | .handle kind _ => HandleKind.ofByte? kind == some .cell
    | _ => false
  | .deferredOf _ _ =>
    match v with
    | .handle kind _ => HandleKind.ofByte? kind == some .promise
    | _ => false
  | .var _ => false
  | .exitOf a e =>
    match v with
    | Val.exitOk x => hasTy x a allocated
    | Value.exitErr written =>
      match causeImage.ofVal written with
      | some c => causeAdmitsP (fun w => hasTy w e allocated) c
      | none => false
    | _ => false
  | .causeOf e =>
    match Val.cause? v with
    | some c => causeAdmitsP (fun w => hasTy w e allocated) c
    | none => false
  | .prod ta tb =>
    match v with
    | .list [x, y] => hasTy x ta allocated && hasTy y tb allocated
    | _ => false
  | .list ty =>
    match v with
    | Value.fiberSnapshot _ =>
      match Val.snapshot? v with
      | some ids => ids.all (fun id => hasTy (Val.fiber id) ty allocated)
      | none => false
    | .list values => values.all fun x => hasTy x ty allocated
    | _ => false
  | .union l r => hasTy v l allocated || hasTy v r allocated
  | .lit value => match v with | .str s => s == value | _ => false
  | .never => false
  | .unknown => true
  | .int => intImage v
  | .except error value =>
    match v with
    | .ctor 0 [err] => hasTy err error allocated
    | .ctor 1 [val] => hasTy val value allocated
    | _ => false
  -- record: the value's names and values against the canonical checkers
  | .record fs =>
    match recordParts? v with
    | some (ns, xs) => namedHasTy (canonF (checkers fs allocated)) ns xs
    | none => false
  -- map: sorted pairs, keys of the key type, values of the value type
  | .map k t =>
    match v with
    | .list es => entriesHasTy (fun a => hasTy a k allocated) (fun x => hasTy x t allocated) es
    | _ => false
  -- T's arms
  | .tuple ts =>
    match v with
    | .list xs => itemsHasTy (itemCheckers ts allocated) xs
    | _ => false
  | .app name _ => handleHasTy name v allocated
  | .null => match v with | .none => true | _ => false
  | .undefined => match v with | .unit => true | _ => false
  | .number => numberImage v
  | .bytes => match v with | .bytes _ => true | _ => false
/-- The field-list companion: one checker per written field, in written order. -/
def checkers (fs : List (String × Bool × Ty)) (allocated : List String) :
    List (String × Bool × (Val → Bool)) :=
  match fs with
  | [] => []
  | (n, o, t) :: rest => (n, o, fun x => hasTy x t allocated) :: checkers rest allocated
/-- The item-list companion. -/
def itemCheckers (ts : List Ty) (allocated : List String) : List (Val → Bool) :=
  match ts with
  | [] => []
  | t :: rest => (fun x => hasTy x t allocated) :: itemCheckers rest allocated
end

/-- A field's checker. -/
def checkerOf (allocated : List String) (c : Bool × Ty) : Bool × (Val → Bool) :=
  (c.1, fun x => hasTy x c.2 allocated)

/-- The companion is a payload map. -/
theorem checkers_eq_map (fs : List (String × Bool × Ty)) (allocated : List String) :
    checkers fs allocated = fs.map (fun q => (q.1, checkerOf allocated q.2)) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, o, t⟩ := p
    rw [checkers, ih]
    rfl

theorem itemCheckers_eq_map (ts : List Ty) (allocated : List String) :
    itemCheckers ts allocated = ts.map (fun t x => hasTy x t allocated) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [itemCheckers, ih]
    rfl

/-- One field is canonical. -/
theorem canonBy_single {β : Type} (p : String × β) : canonF [p] = [p] := rfl

/-- **The record arm**, read through the canonical fields: a value with parts. -/
theorem hasTy_record {v : Val} {ns xs : List Val} (hv : recordParts? v = some (ns, xs))
    (fs : List (String × Bool × Ty)) (allocated : List String) :
    hasTy v (.record fs) allocated =
      namedHasTy ((canonF fs).map (fun q => (q.1, checkerOf allocated q.2))) ns xs := by
  rw [hasTy, hv, checkers_eq_map, canonBy_map]

/-- A value without record parts is no record's member. -/
theorem hasTy_record_none {v : Val} (hv : recordParts? v = none)
    (fs : List (String × Bool × Ty)) (allocated : List String) :
    hasTy v (.record fs) allocated = false := by
  rw [hasTy, hv]

/-- The tuple arm. -/
theorem hasTy_tuple (xs : List Val) (ts : List Ty) (allocated : List String) :
    hasTy (.list xs) (.tuple ts) allocated = itemsHasTy (ts.map (fun t x => hasTy x t allocated)) xs := by
  rw [hasTy, itemCheckers_eq_map]

/-- A pair tuple and a product have the same members (so `tuple [a, b]` may normalize to
`prod a b`). -/
theorem hasTy_tuple_pair (v : Val) (a b : Ty) (allocated : List String) :
    hasTy v (.tuple [a, b]) allocated = hasTy v (.prod a b) allocated := by
  cases v
  case list xs =>
    rw [hasTy_tuple]
    match xs with
    | [] => rfl
    | [_] => simp only [List.map_cons, List.map_nil, itemsHasTy, Bool.and_false, hasTy]
    | [x, y] => simp only [List.map_cons, List.map_nil, itemsHasTy, Bool.and_true, hasTy]
    | _ :: _ :: _ :: _ => simp only [List.map_cons, List.map_nil, itemsHasTy, Bool.and_false, hasTy]
  all_goals rfl

/-! ## The leaf table's membership obligation: one lemma per edge

A leaf head's members are its representative's (`leafRep`; a literal's is `string`, the union of
every literal's members). A type's members are among its head's representative's
(`hasTy_leafRep`), and at a payload-free head the two are one (`hasTy_of_leafRep`). An edge's
obligation is the inclusion of its source's representative's members in its target's
(`hasTy_leafEdge`: one line per edge); the closure needs nothing more, because a path carries the
inclusion edge by edge (`hasTy_leafPath`). -/

/-- A leaf head's representative type. -/
def leafRep : LeafHead → Ty
  | .lit => .string
  | .string => .string
  | .nat => .nat
  | .int => .int
  | .number => .number
  | .undefined => .undefined
  | .unit => .unit

/-- No edge enters `lit`: a payload head is only ever a source (checked over the table). -/
theorem leafEdges_target_ne_lit : ∀ e ∈ leafEdges, e.2 ≠ .lit := by decide

/-- A path ends where it starts or at some edge's target. -/
theorem Ty.LeafPath.target {E : List (LeafHead × LeafHead)} {x y : LeafHead} (h : LeafPath E x y) :
    x = y ∨ ∃ e ∈ E, e.2 = y := by
  induction h with
  | refl => exact Or.inl rfl
  | step he _ ih =>
    rcases ih with rfl | ⟨e', he', rfl⟩
    · exact Or.inr ⟨_, he, rfl⟩
    · exact Or.inr ⟨e', he', rfl⟩

theorem hasTy_leafRep {t : Ty} {x : LeafHead} (h : leafHead t = some x) (v : Val)
    (allocated : List String) (hv : hasTy v t allocated = true) :
    hasTy v (leafRep x) [] = true := by
  cases t
  case lit s =>
    cases h
    cases v
    case str => rfl
    all_goals exact Bool.noConfusion hv
  case string | nat | int | number | undefined | unit => cases h; cases v <;> exact hv
  all_goals cases h

theorem hasTy_of_leafRep {t : Ty} {x : LeafHead} (h : leafHead t = some x) (hx : x ≠ .lit)
    (v : Val) (allocated : List String) (hv : hasTy v (leafRep x) [] = true) :
    hasTy v t allocated = true := by
  cases t
  case lit => cases h; exact absurd rfl hx
  case string | nat | int | number | undefined | unit => cases h; cases v <;> exact hv
  all_goals cases h

theorem hasTy_nat_int (v : Val) (hv : hasTy v .nat [] = true) : hasTy v .int [] = true := by
  cases v
  case nat => rfl
  all_goals exact Bool.noConfusion hv

theorem hasTy_int_number (v : Val) (hv : hasTy v .int [] = true) : hasTy v .number [] = true := by
  show (intImage v || _) = true
  rw [show intImage v = true from hv, Bool.true_or]

/-- **The membership obligation of the leaf table, one line per edge.** -/
theorem hasTy_leafEdge {x y : LeafHead} (he : (x, y) ∈ leafEdges) (v : Val)
    (hv : hasTy v (leafRep x) [] = true) : hasTy v (leafRep y) [] = true := by
  simp only [leafEdges, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hv                            -- lit → string: the representative is `string` itself
  · exact hasTy_nat_int v hv            -- nat → int
  · exact hasTy_int_number v hv         -- int → number
  · cases v <;> exact hv                -- undefined → unit: one image

theorem hasTy_leafPath {x y : LeafHead} (h : LeafPath leafEdges x y) (v : Val)
    (hv : hasTy v (leafRep x) [] = true) : hasTy v (leafRep y) [] = true := by
  induction h with
  | refl => exact hv
  | step he _ ih => exact ih (hasTy_leafEdge he v hv)

/-- **The table's rule keeps membership**: no edge is named. -/
theorem hasTy_leafRule {a b : Ty} (h : leafRule a b = true) (v : Val) (allocated : List String)
    (hv : hasTy v a allocated = true) : hasTy v b allocated = true := by
  obtain ⟨x, y, hx, hy, hxy, hle⟩ := leafRule_eq_true h
  have hpath := leafLe_iff_path.mp hle
  have hy_ne : y ≠ .lit := by
    rcases hpath.target with rfl | ⟨e, he, rfl⟩
    · exact absurd rfl hxy
    · exact leafEdges_target_ne_lit e he
  exact hasTy_of_leafRep hy hy_ne v allocated
    (hasTy_leafPath hpath v (hasTy_leafRep hx v allocated hv))

/-! ## Membership respects `sub` -/

/-- **Monotonicity of the named read**: under one list of names, a field optional where it was
required (the flag implication) and a checker that admits more admit more. -/
theorem namedHasTy_mono :
    ∀ (cf cg : List (String × Bool × (Val → Bool))) (ns xs : List Val),
      cf.map Prod.fst = cg.map Prod.fst →
      (∀ p ∈ cf.zip cg, (p.1.2.1 = true → p.2.2.1 = true) ∧
        ∀ x, p.1.2.2 x = true → p.2.2.2 x = true) →
      namedHasTy cf ns xs = true → namedHasTy cg ns xs = true
  | [], [], _, _, _, _, h => h
  | [], _ :: _, _, _, hh, _, _ => nomatch hh
  | _ :: _, [], _, _, hh, _, _ => nomatch hh
  | (n, o, c) :: cf, (m, p, d) :: cg, ns, xs, hh, hpt, h => by
    simp only [List.map_cons, List.cons.injEq] at hh
    obtain ⟨rfl, hrest⟩ := hh
    obtain ⟨hop, hc⟩ := hpt ((n, o, c), (n, p, d)) List.mem_cons_self
    have hpt' : ∀ q ∈ cf.zip cg, (q.1.2.1 = true → q.2.2.1 = true) ∧
        ∀ x, q.1.2.2 x = true → q.2.2.2 x = true :=
      fun q hq => hpt q (List.mem_cons_of_mem _ hq)
    match ns, xs, h with
    | [], [], h =>
      simp only [namedHasTy, Bool.and_eq_true] at h ⊢
      exact ⟨hop h.1, namedHasTy_mono cf cg [] [] hrest hpt' h.2⟩
    | [], _ :: _, h => exact Bool.noConfusion h
    | v0 :: _, [], h => cases v0 <;> exact Bool.noConfusion h
    | v0 :: ns, x :: xs, h =>
      cases v0 with
      | str k =>
        simp only [namedHasTy] at h ⊢
        by_cases hk : k = n
        · rw [if_pos hk, Bool.and_eq_true] at h
          rw [if_pos hk, Bool.and_eq_true]
          exact ⟨hc x h.1, namedHasTy_mono cf cg ns xs hrest hpt' h.2⟩
        · rw [if_neg hk, Bool.and_eq_true] at h
          rw [if_neg hk, Bool.and_eq_true]
          exact ⟨hop h.1, namedHasTy_mono cf cg (.str k :: ns) (x :: xs) hrest hpt' h.2⟩
      | _ => exact Bool.noConfusion h

/-- Pointwise stronger checkers of one arity admit more (the tuple read). -/
theorem itemsHasTy_mono :
    ∀ (xs : List Val) (cs ds : List (Val → Bool)), cs.length = ds.length →
      (∀ p ∈ cs.zip ds, ∀ x, p.1 x = true → p.2 x = true) →
      itemsHasTy cs xs = true → itemsHasTy ds xs = true
  | [], [], [], _, _, _ => rfl
  | x :: xs, c :: cs, d :: ds, hlen, hpt, h => by
    simp only [itemsHasTy, Bool.and_eq_true] at h ⊢
    exact ⟨hpt (c, d) List.mem_cons_self x h.1,
      itemsHasTy_mono xs cs ds (Nat.succ.inj hlen)
        (fun p hp => hpt p (List.mem_cons_of_mem _ hp)) h.2⟩
  | [], [], _ :: _, hlen, _, _ => nomatch hlen
  | [], _ :: _, _, _, _, h => Bool.noConfusion h
  | _ :: _, [], _, _, _, h => Bool.noConfusion h
  | _ :: _, _ :: _, [], hlen, _, _ => nomatch hlen

/-- Equal heads agree position by position on the flag. -/
theorem heads_zip : ∀ (l l' : List (String × Bool × Ty)), heads l = heads l' →
    ∀ q ∈ l.zip l', q.1.2.1 = q.2.2.1
  | [], _, _, q, hq => by simp only [List.zip_nil_left, List.not_mem_nil] at hq
  | _ :: _, [], _, q, hq => by simp only [List.zip_nil_right, List.not_mem_nil] at hq
  | p :: l, p' :: l', h, q, hq => by
    simp only [heads, List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    rw [List.zip_cons_cons, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact h.1.2
    · exact heads_zip l l' h.2 q hq

theorem sortedEntries_entries {ck cv ck' cv' : Val → Bool} (hk : ∀ a, ck a = true → ck' a = true)
    (hv : ∀ x, cv x = true → cv' x = true) (es : List Val)
    (h : entriesHasTy ck cv es = true) : entriesHasTy ck' cv' es = true := by
  unfold entriesHasTy at h ⊢
  rw [Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨h.1, fun e he => ?_⟩
  have := h.2 e he
  cases e
  case pair a x =>
    simp only [Bool.and_eq_true] at this ⊢
    exact ⟨hk a this.1, hv x this.2⟩
  all_goals exact this

/-- **Membership respects `sub`** (`hasTy_sub`; production derives it from `cata_admits_sub`,
whose `AdmitsSub` gains a field per appended arm and loses its literal field to the table's).
By `fun_induction sub`: `case2` is the table's line, discharged by `hasTy_leafRule` without naming
an edge. -/
theorem hasTy_sub {a b : Ty} (hsub : sub a b = true) :
    ∀ v allocated, hasTy v a allocated = true → hasTy v b allocated = true := by
  fun_induction sub a b
  case case1 => intro v al h; exact h
  case case2 _ hl => intro v al h; exact hasTy_leafRule hl v al h
  case case3 => intro v al h; simp only [hasTy, Bool.false_eq_true] at h
  case case4 a1 a2 b _ _ iha ihb =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v al h
    simp only [hasTy, Bool.or_eq_true] at h
    exact h.elim (iha h1 v al) (ihb h2 v al)
  case case5 a b1 b2 _ _ _ _ iha ihb =>
    intro v al h
    simp only [hasTy, Bool.or_eq_true]
    exact (Bool.or_eq_true_iff.mp hsub).elim (fun hx => Or.inl (iha hx v al h))
      (fun hx => Or.inr (ihb hx v al h))
  case case6 => intro v al _; simp only [hasTy]
  case case7 x y _ _ ih =>
    intro v al h
    simp only [hasTy] at h ⊢
    split at h
    · rfl
    · rename_i z
      exact ih hsub z al h
    · exact Bool.noConfusion h
  case case8 x y _ _ ih =>
    intro v al h
    simp only [hasTy] at h ⊢
    split at h
    · rename_i p
      split at h
      · rename_i ids hids
        simp only [List.all_eq_true] at h ⊢
        exact fun id hid => ih hsub _ al (h id hid)
      · exact Bool.noConfusion h
    · rw [List.all_eq_true] at h ⊢
      exact fun z hz => ih hsub z al (h z hz)
    · exact Bool.noConfusion h
  case case9 a1 a2 b1 b2 _ _ iha ihb =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v al h
    simp only [hasTy] at h ⊢
    split at h
    · rw [Bool.and_eq_true] at h ⊢
      exact ⟨iha h1 _ al h.1, ihb h2 _ al h.2⟩
    · exact Bool.noConfusion h
  case case10 e1 a1 e2 a2 _ _ ihe iha =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v al h
    simp only [hasTy] at h ⊢
    split at h
    · exact ihe h1 _ al h
    · exact iha h2 _ al h
    · exact Bool.noConfusion h
  case case11 a1 e1 a2 e2 _ _ iha ihe =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v al h
    simp only [hasTy] at h ⊢
    split at h
    · exact iha h1 _ al h
    · split at h
      · rename_i c _
        exact causeAdmitsP_mono (fun w hw => ihe h2 w al hw) c h
      · exact Bool.noConfusion h
    · exact Bool.noConfusion h
  case case12 e1 e2 _ _ ih =>
    intro v al h
    simp only [hasTy] at h ⊢
    split at h
    · rename_i c _
      exact causeAdmitsP_mono (fun w hw => ih hsub w al hw) c h
    · exact Bool.noConfusion h
  case case13 =>
    intro v al h
    simp only [hasTy] at h ⊢
    exact h
  case case14 =>
    intro v al h
    simp only [hasTy] at h ⊢
    exact h
  case case15 =>
    intro v al h
    simp only [hasTy] at h ⊢
    exact h
  case case16 fs gs _ _ ih =>
    obtain ⟨hh, hall⟩ := Bool.and_eq_true_iff.mp hsub
    have hh' : heads (canonF fs) = heads (canonF gs) := of_decide_eq_true hh
    have hall' : ((canonF fs).zip (canonF gs)).all (fun pq => sub pq.1.2.2 pq.2.2.2) = true := by
      rw [← all_zip_attach (fun p q : String × Bool × Ty => sub p.2.2 q.2.2)]
      exact hall
    rw [List.all_eq_true] at hall'
    intro v al h
    cases hv : recordParts? v with
    | none => rw [hasTy_record_none hv] at h; exact Bool.noConfusion h
    | some parts =>
      obtain ⟨ns, xs⟩ := parts
      rw [hasTy_record hv] at h ⊢
      refine namedHasTy_mono _ _ ns xs ?_ ?_ h
      · have hn := congrArg (List.map Prod.fst) hh'
        simp only [heads, List.map_map, Function.comp_def] at hn ⊢
        exact hn
      · intro p hp
        rw [List.zip_map, List.mem_map] at hp
        obtain ⟨⟨q1, q2⟩, hq, rfl⟩ := hp
        have hq1 : q1 ∈ canonF fs := (List.of_mem_zip hq).1
        have hq2 : q2 ∈ canonF gs := (List.of_mem_zip hq).2
        refine ⟨fun hf => ?_, fun x hx => ih ⟨⟨q1, hq1⟩, ⟨q2, hq2⟩⟩ (hall' (q1, q2) hq) x al hx⟩
        have he : q1.2.1 = q2.2.1 := heads_zip _ _ hh' (q1, q2) hq
        show q2.2.1 = true
        rw [← he]
        exact hf
  case case17 k1 v1 k2 v2 _ _ ihk _ ihv =>
    obtain ⟨hk12, hv⟩ := Bool.and_eq_true_iff.mp hsub
    obtain ⟨hk, _⟩ := Bool.and_eq_true_iff.mp hk12
    intro v al h
    simp only [hasTy] at h ⊢
    split at h
    · exact sortedEntries_entries (fun a ha => ihk hk a al ha) (fun x hx => ihv hv x al hx) _ h
    · exact Bool.noConfusion h
  case case18 ts us _ _ ih =>
    obtain ⟨hlen, hall⟩ := Bool.and_eq_true_iff.mp hsub
    have hlen' : ts.length = us.length := of_decide_eq_true hlen
    have hall' : (ts.zip us).all (fun pq => sub pq.1 pq.2) = true := by
      rw [← all_zip_attach (fun p q : Ty => sub p q)]
      exact hall
    rw [List.all_eq_true] at hall'
    intro v al h
    cases v
    case list xs =>
      rw [hasTy_tuple] at h ⊢
      refine itemsHasTy_mono xs _ _ (by rw [List.length_map, List.length_map, hlen']) ?_ h
      intro p hp x hx
      rw [List.zip_map, List.mem_map] at hp
      obtain ⟨⟨t, u⟩, htu, rfl⟩ := hp
      exact ih ⟨⟨t, (List.of_mem_zip htu).1⟩, ⟨u, (List.of_mem_zip htu).2⟩⟩ (hall' (t, u) htu) x al hx
    all_goals simp only [hasTy, Bool.false_eq_true] at h
  case case19 n ts m us _ _ _ =>
    obtain ⟨hnm, _⟩ := Bool.and_eq_true_iff.mp hsub
    obtain ⟨rfl, _⟩ := of_decide_eq_true hnm
    intro v al h
    simp only [hasTy] at h ⊢
    exact h
  case case20 => exact Bool.noConfusion hsub

/-! ## Normalization keeps membership (R3.2), no premise -/

/-- copied. -/
theorem hasTy_ofMembers (v : Val) (xs : List Ty) (al : List String) :
    hasTy v (ofMembers xs) al = xs.any (fun t => hasTy v t al) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => simp only [ofMembers, List.any_cons, List.any_nil, Bool.or_false]
    | cons y ys =>
      change (hasTy v x al || hasTy v (ofMembers (y :: ys)) al) = _
      rw [ih]
      rfl

/-- copied text (rewritten without the production's `try`). -/
theorem hasTy_members (v : Val) (t : Ty) (al : List String) :
    t.members.any (fun t => hasTy v t al) = hasTy v t al := by
  induction t with
  | union a b iha ihb =>
    rw [members, List.any_append, iha, ihb]
    simp only [hasTy]
  | never => simp only [members, List.any_nil, hasTy]
  | _ => simp only [members, List.any_cons, List.any_nil, Bool.or_false]

/-- copied. -/
theorem any_row_normalize (xs : List Ty) (p : Ty → Bool) :
    (Effect4.Row.normalize xs).elems.any p = xs.any p := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨t, ht, hp⟩
    exact ⟨t, (Effect4.Row.mem_normalize t xs).mp ht, hp⟩
  · rintro ⟨t, ht, hp⟩
    exact ⟨t, (Effect4.Row.mem_normalize t xs).mpr ht, hp⟩

/-- copied. -/
theorem hasTy_normalizeRow (v : Val) (xs : List Ty) (al : List String) :
    (normalizeRow xs).elems.any (fun t => hasTy v t al) = xs.any (fun t => hasTy v t al) := by
  rw [← any_row_normalize xs (fun t => hasTy v t al)]
  apply Bool.eq_iff_iff.mpr
  simp only [normalizeRow, List.any_eq_true]
  constructor
  · rintro ⟨t, ht, hv⟩
    exact ⟨t, Effect4.Row.antichain_subset sub ht, hv⟩
  · rintro ⟨t, ht, hv⟩
    obtain ⟨u, hu, htu⟩ := Effect4.Row.antichain_coverage sub sub_refl sub_trans
      (Effect4.Row.normalize xs).elems t ht
    exact ⟨u, hu, hasTy_sub htu v al hv⟩

/-- copied. -/
theorem hasTy_factors (v : Val) (t : Ty) (al : List String) :
    t.factors.any (fun t => hasTy v t al) = hasTy v t al := by
  cases t with
  | never => rfl
  | _ => exact hasTy_members v _ al

/-- copied. -/
theorem hasTy_productMembers (v : Val) (a b : Ty) (al : List String) :
    (productMembers a b).any (fun t => hasTy v t al) = hasTy v (.prod a b) al := by
  simp only [productMembers, List.any_flatMap, List.any_map, Function.comp_def]
  simp only [hasTy]
  split
  · rename_i x y
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, Bool.and_eq_true]
    constructor
    · rintro ⟨ta, hta, tb, htb, hx, hy⟩
      exact ⟨(Bool.eq_iff_iff.mp (hasTy_factors x a al)).mp (List.any_eq_true.mpr ⟨ta, hta, hx⟩),
        (Bool.eq_iff_iff.mp (hasTy_factors y b al)).mp (List.any_eq_true.mpr ⟨tb, htb, hy⟩)⟩
    · rintro ⟨hx, hy⟩
      obtain ⟨ta, hta, hx⟩ := List.any_eq_true.mp ((Bool.eq_iff_iff.mp (hasTy_factors x a al)).mpr hx)
      obtain ⟨tb, htb, hy⟩ := List.any_eq_true.mp ((Bool.eq_iff_iff.mp (hasTy_factors y b al)).mpr hy)
      exact ⟨ta, hta, tb, htb, hx, hy⟩
  · apply List.any_eq_false.mpr
    intro x _ h
    obtain ⟨_, _, h⟩ := List.any_eq_true.mp h
    exact Bool.false_ne_true h

theorem causeAdmitsP_congr {f g : Val → Bool} (h : ∀ w, f w = g w) (c : CauseV) :
    causeAdmitsP f c = causeAdmitsP g c := by
  rw [show f = g from funext h]

/-- The product case of `hasTy_normalize`, given the two components' (the production proof's
`prod` arm, extracted so the pair tuple reads it). -/
theorem hasTy_normalize_prod (a b : Ty) (v : Val) (al : List String)
    (iha : ∀ v, hasTy v a.normalize al = hasTy v a al)
    (ihb : ∀ v, hasTy v b.normalize al = hasTy v b al) :
    hasTy v (normalize (.prod a b)) al = hasTy v (.prod a b) al := by
  rw [normalize, hasTy_ofMembers, hasTy_normalizeRow, hasTy_productMembers]
  simp only [hasTy]
  split
  · rw [iha, ihb]
  · rfl

/-- The record case of `hasTy_normalize`, named. The canonical read is invariant because
normalizing a record maps its canonical list (names and flags kept), and the checker of a
normalized field type is the checker of the field type (the induction hypothesis). -/
theorem hasTy_normalize_record (fs : List (String × Bool × Ty)) (v : Val) (al : List String)
    (ih : ∀ p ∈ fs, ∀ v, hasTy v (normalize p.2.2) al = hasTy v p.2.2 al) :
    hasTy v (normalize (.record fs)) al = hasTy v (.record fs) al := by
  rw [normalize_record]
  cases hv : recordParts? v with
  | none => rw [hasTy_record_none hv, hasTy_record_none hv]
  | some parts =>
    obtain ⟨ns, xs⟩ := parts
    rw [hasTy_record hv, hasTy_record hv,
      canonBy_of_ascending _ (ascending_map normPayload (canonBy_ascending fs)), List.map_map]
    congr 1
    apply List.map_congr_left
    intro q hq
    have hfun : (fun x => hasTy x (normalize q.2.2) al) = fun x => hasTy x q.2.2 al :=
      funext fun x => ih q (mem_canonBy hq) x
    simp only [Function.comp_apply, checkerOf, normPayload]
    rw [hfun]

/-- The tuple case: a pair is a product; any other arity in place, item by item. -/
theorem hasTy_normalize_tuple (ts : List Ty) (v : Val) (al : List String)
    (ih : ∀ t ∈ ts, ∀ v, hasTy v (normalize t) al = hasTy v t al) :
    hasTy v (normalize (.tuple ts)) al = hasTy v (.tuple ts) al := by
  by_cases h2 : ts.length = 2
  · match ts, h2, ih with
    | [a, b], _, ih =>
      rw [hasTy_tuple_pair]
      exact hasTy_normalize_prod a b v al (ih a List.mem_cons_self)
        (ih b (List.mem_cons_of_mem _ List.mem_cons_self))
  · rw [normalize_tuple_of_ne ts h2, normalizeItems_eq_map]
    cases v
    case list xs =>
      rw [hasTy_tuple, hasTy_tuple, List.map_map]
      congr 1
      apply List.map_congr_left
      intro t ht
      funext x
      exact ih t ht x
    all_goals rfl

/-- The reference case: membership reads the name only, and `app n []` is `handle n`. -/
theorem hasTy_normalize_app (n : String) (ts : List Ty) (v : Val) (al : List String) :
    hasTy v (normalize (.app n ts)) al = hasTy v (.app n ts) al := by
  cases ts with
  | nil => rfl
  | cons t ts => rw [normalize_app_of_ne n _ (List.cons_ne_nil _ _)]; rfl

/-- **Normalization keeps membership at every type, with no premise.** case: five (record, map,
tuple, reference, and the four leaves at `rfl`); the production proof's other arms are its named
congruence facts, inlined here. -/
theorem hasTy_normalize (t : Ty) (v : Val) (al : List String) :
    hasTy v t.normalize al = hasTy v t al := by
  induction t generalizing v with
  | never => rfl
  | unknown | unit | nat | int | string | bool | handle | lit | fiberOf | refOf | deferredOf | var
  | null | undefined | number | bytes => rfl
  | union a b iha ihb =>
    rw [normalize, hasTy_ofMembers, hasTy_normalizeRow, List.any_append,
      hasTy_members, hasTy_members, iha, ihb]
    rfl
  | prod a b iha ihb => exact hasTy_normalize_prod a b v al iha ihb
  | option t ih =>
    show hasTy v (.option t.normalize) al = hasTy v (.option t) al
    simp only [hasTy]
    split
    · rfl
    · exact ih _
    · rfl
  | list t ih =>
    show hasTy v (.list t.normalize) al = hasTy v (.list t) al
    simp only [hasTy]
    split
    · split
      · exact List.all_congr rfl (fun id => ih (Val.fiber id))
      · rfl
    · exact List.all_congr rfl ih
    · rfl
  | except e a ihe iha =>
    show hasTy v (.except e.normalize a.normalize) al = hasTy v (.except e a) al
    simp only [hasTy]
    split
    · exact ihe _
    · exact iha _
    · rfl
  | exitOf a e iha ihe =>
    show hasTy v (.exitOf a.normalize e.normalize) al = hasTy v (.exitOf a e) al
    simp only [hasTy]
    split
    · exact iha _
    · split
      · exact causeAdmitsP_congr ihe _
      · rfl
    · rfl
  | causeOf e ih =>
    show hasTy v (.causeOf e.normalize) al = hasTy v (.causeOf e) al
    simp only [hasTy]
    split
    · exact causeAdmitsP_congr ih _
    · rfl
  | record fs ih => exact hasTy_normalize_record fs v al (fun p hp w => ih p hp w)
  | map k t ihk iht =>
    show hasTy v (.map k.normalize t.normalize) al = hasTy v (.map k t) al
    simp only [hasTy]
    split
    · rw [show (fun a => hasTy a k.normalize al) = (fun a => hasTy a k al) from funext ihk,
        show (fun x => hasTy x t.normalize al) = (fun x => hasTy x t al) from funext iht]
    · rfl
  | tuple ts ih => exact hasTy_normalize_tuple ts v al (fun t ht w => ih t ht w)
  | app n ts => exact hasTy_normalize_app n ts v al

/-- copied: membership in the join. -/
theorem hasTy_join_left (a b : Ty) (v : Val) (al : List String) (hv : hasTy v a al = true) :
    hasTy v (join a b) al = true := by
  rw [← hasTy_normalize a v al] at hv
  exact hasTy_sub (sub_normalize_union_left a b) v al hv

theorem hasTy_join_right (a b : Ty) (v : Val) (al : List String) (hv : hasTy v b al = true) :
    hasTy v (join a b) al = true := by
  rw [← hasTy_normalize b v al] at hv
  exact hasTy_sub (sub_normalize_union_right a b) v al hv

/-! ## Width is refused by the names; an optional key's absence; the incompleteness (TY-10) -/

/-- The empty read accepts only the empty value. -/
theorem namedHasTy_nil {ns xs : List Val} (h : namedHasTy [] ns xs = true) : ns = [] ∧ xs = [] := by
  match ns, xs, h with
  | [], [], _ => exact ⟨rfl, rfl⟩
  | [], _ :: _, h => exact Bool.noConfusion h
  | _ :: _, _, h => exact Bool.noConfusion h

/-- **The names a read accepts, at a type whose fields are all required, are exactly the
canonical names.** -/
theorem namedHasTy_names :
    ∀ (cs : List (String × Bool × (Val → Bool))) (ns xs : List Val),
      (∀ c ∈ cs, c.2.1 = false) → namedHasTy cs ns xs = true → ns = cs.map (fun c => .str c.1)
  | [], ns, xs, _, h => (namedHasTy_nil h).1
  | (n, o, c) :: cs, ns, xs, hreq, h => by
    have ho : o = false := hreq (n, o, c) List.mem_cons_self
    subst ho
    have hreq' : ∀ c ∈ cs, c.2.1 = false := fun c hc => hreq c (List.mem_cons_of_mem _ hc)
    match ns, xs, h with
    | [], [], h => exact Bool.noConfusion h
    | [], _ :: _, h => exact Bool.noConfusion h
    | v0 :: _, [], h => cases v0 <;> exact Bool.noConfusion h
    | v0 :: ns, x :: xs, h =>
      cases v0 with
      | str k =>
        simp only [namedHasTy] at h
        by_cases hk : k = n
        · rw [if_pos hk, Bool.and_eq_true] at h
          rw [hk, namedHasTy_names cs ns xs hreq' h.2]
          rfl
        · rw [if_neg hk, Bool.false_and] at h
          exact Bool.noConfusion h
      | _ => exact Bool.noConfusion h

/-- **Width is refused by the names** (row 165 (a)): a value is a member of two all-required
record types only when their canonical name lists are equal. The positional clause's width
facts (`fits_coerce`, the unsound width rule) have no analogue: a value names its fields. -/
theorem record_width_refused (v : Val) (fs gs : List (String × Bool × Ty)) (al : List String)
    (hf : ∀ p ∈ fs, p.2.1 = false) (hg : ∀ p ∈ gs, p.2.1 = false)
    (hvf : hasTy v (.record fs) al = true) (hvg : hasTy v (.record gs) al = true) :
    (canonF fs).map Prod.fst = (canonF gs).map Prod.fst := by
  cases hv : recordParts? v with
  | none => rw [hasTy_record_none hv] at hvf; exact Bool.noConfusion hvf
  | some parts =>
    obtain ⟨ns, xs⟩ := parts
    rw [hasTy_record hv] at hvf hvg
    have reqOf : ∀ (l : List (String × Bool × Ty)), (∀ p ∈ l, p.2.1 = false) →
        ∀ c ∈ (canonF l).map (fun q => (q.1, checkerOf al q.2)), c.2.1 = false := by
      intro l hl c hc
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
      exact hl q (mem_canonBy hq)
    have h1 := namedHasTy_names _ ns xs (reqOf fs hf) hvf
    have h2 := namedHasTy_names _ ns xs (reqOf gs hg) hvg
    rw [h1, List.map_map, List.map_map] at h2
    have hinj : ∀ (l l' : List (String × Bool × Ty)),
        l.map ((fun c => Val.str c.1) ∘ fun q => (q.1, checkerOf al q.2)) =
          l'.map ((fun c => Val.str c.1) ∘ fun q => (q.1, checkerOf al q.2)) →
        l.map Prod.fst = l'.map Prod.fst := by
      intro l
      induction l with
      | nil =>
        intro l' h
        cases l' with
        | nil => rfl
        | cons _ _ => exact absurd h (List.cons_ne_nil _ _).symm
      | cons q l ih =>
        intro l' h
        cases l' with
        | nil => exact absurd h (List.cons_ne_nil _ _)
        | cons q' l' =>
          simp only [List.map_cons, List.cons.injEq, Function.comp_apply] at h ⊢
          refine ⟨?_, ih l' h.2⟩
          injection h.1
    exact hinj _ _ h2

/-- An optional key's absence: the field is absent from both lists, and the read skips it. -/
theorem namedHasTy_absent (n : String) (c : Val → Bool) (cs : List (String × Bool × (Val → Bool)))
    (ns xs : List Val) (h : namedHasTy cs ns xs = true) (hfresh : ∀ k, .str k ∈ ns → k ≠ n) :
    namedHasTy ((n, true, c) :: cs) ns xs = true := by
  match ns, xs with
  | [], [] =>
    simp only [namedHasTy, Bool.true_and]
    exact h
  | [], _ :: _ => cases cs <;> exact Bool.noConfusion h
  | v0 :: _, [] => cases v0 <;> cases cs <;> exact Bool.noConfusion h
  | v0 :: ns, x :: xs =>
    cases v0 with
    | str k =>
      simp only [namedHasTy]
      rw [if_neg (hfresh k List.mem_cons_self), Bool.true_and]
      exact h
    | _ => cases cs <;> exact Bool.noConfusion h

/-- **Required is below optional in membership** (the named clause; question 4a): a value whose
names include a required field's is a member when that field is optional. The copy's `sub` keeps
flags exact (`heads` compares them): admitting this edge makes the record head an order, not an
equality, which `sub_eq_args`'s shape does not have (`note.md`). -/
theorem record_required_below_optional (v : Val) (n : String) (t : Ty) (al : List String)
    (h : hasTy v (.record [(n, false, t)]) al = true) : hasTy v (.record [(n, true, t)]) al = true := by
  cases hv : recordParts? v with
  | none => rw [hasTy_record_none hv] at h; exact Bool.noConfusion h
  | some parts =>
    obtain ⟨ns, xs⟩ := parts
    rw [hasTy_record hv, canonBy_single] at h ⊢
    refine namedHasTy_mono _ _ ns xs ?_ ?_ h
    · rfl
    intro p hp
    simp only [List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_left,
      List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    exact ⟨fun _ => rfl, fun _ hx => hx⟩

/-- A one-field required record's read. -/
theorem namedHasTy_one (n : String) (c : Val → Bool) (ns xs : List Val) :
    namedHasTy [(n, false, c)] ns xs = true ↔ ∃ x, ns = [.str n] ∧ xs = [x] ∧ c x = true := by
  constructor
  · intro h
    match ns, xs, h with
    | [], [], h => exact Bool.noConfusion h
    | [], _ :: _, h => exact Bool.noConfusion h
    | v0 :: _, [], h => cases v0 <;> exact Bool.noConfusion h
    | v0 :: ns, x :: xs, h =>
      cases v0 with
      | str k =>
        simp only [namedHasTy] at h
        by_cases hk : k = n
        · rw [if_pos hk, Bool.and_eq_true] at h
          obtain ⟨rfl, rfl⟩ := namedHasTy_nil h.2
          exact ⟨x, by rw [hk], rfl, h.1⟩
        · rw [if_neg hk, Bool.false_and] at h
          exact Bool.noConfusion h
      | _ => exact Bool.noConfusion h
  · rintro ⟨x, rfl, rfl, hx⟩
    simp only [namedHasTy, ↓reduceIte, hx, Bool.and_self]

/-- A record with one union-typed field, and the union of the two records it would distribute
into. Records are factors (row 119 (d)): `normalize` keeps the first as one member. -/
def recordOfUnion : Ty := .record [("a", false, .union .nat .string)]
def unionOfRecords : Ty := .union (.record [("a", false, .nat)]) (.record [("a", false, .string)])

/-- A one-field record's membership through the one-field read. -/
theorem hasTy_record_one {v : Val} {ns xs : List Val} (hv : recordParts? v = some (ns, xs))
    (n : String) (t : Ty) (al : List String) :
    hasTy v (.record [(n, false, t)]) al = namedHasTy [(n, false, fun x => hasTy x t al)] ns xs := by
  rw [hasTy_record hv, canonBy_single]
  rfl

/-- **`record_sub_not_complete`** (proved), named: the two have exactly the same members, the
second is below the first, and the first is not below the second. The `sub_not_complete` kind
(`Laws/Program/Template.lean:322`), at records. -/
theorem record_sub_not_complete :
    (∀ v al, hasTy v recordOfUnion al = hasTy v unionOfRecords al) ∧
      sub unionOfRecords recordOfUnion = true ∧ sub recordOfUnion unionOfRecords = false := by
  refine ⟨fun v al => ?_, by decide +kernel, by decide +kernel⟩
  cases hv : recordParts? v with
  | none =>
    show hasTy v (.record _) al = (hasTy v (.record _) al || hasTy v (.record _) al)
    rw [hasTy_record_none hv, hasTy_record_none hv, hasTy_record_none hv]
    rfl
  | some parts =>
    obtain ⟨ns, xs⟩ := parts
    show hasTy v (.record [("a", false, .union .nat .string)]) al =
      (hasTy v (.record [("a", false, .nat)]) al || hasTy v (.record [("a", false, .string)]) al)
    rw [hasTy_record_one hv, hasTy_record_one hv, hasTy_record_one hv]
    apply Bool.eq_iff_iff.mpr
    rw [Bool.or_eq_true, namedHasTy_one, namedHasTy_one, namedHasTy_one]
    constructor
    · rintro ⟨x, hn, hx, hc⟩
      rcases Bool.or_eq_true_iff.mp hc with h | h
      · exact Or.inl ⟨x, hn, hx, h⟩
      · exact Or.inr ⟨x, hn, hx, h⟩
    · rintro (⟨x, hn, hx, h⟩ | ⟨x, hn, hx, h⟩)
      · exact ⟨x, hn, hx, Bool.or_eq_true_iff.mpr (Or.inl h)⟩
      · exact ⟨x, hn, hx, Bool.or_eq_true_iff.mpr (Or.inr h)⟩

/-! ## The red control for the number tower's encoding -/

/-- Lean's generated `Int` image (`Int.ofNat n ↦ ctor 0 [nat n]`, `Int.negSucc k ↦ ctor 1 [nat k]`,
the `Image` deriving's constructor-index layout). -/
def generatedIntImage : Val → Bool
  | .ctor 0 [.nat _] => true
  | .ctor 1 [.nat _] => true
  | _ => false

/-- **Red control**: under the generated image, a natural's value is not an integer's, so the
table's edge `nat ⊑ int` would break `hasTy_sub` (whose `nat → int` line, `hasTy_nat_int`, reads the
stand-in `intImage`). -/
theorem generated_int_image_breaks_tower :
    ¬ ∀ v, hasTy v .nat [] = true → generatedIntImage v = true := by
  intro h
  exact Bool.noConfusion (h (.nat 3) rfl)

-- The normal form keeps the record of a union as one member (records are factors), while a
-- product of the same union distributes.
#guard (normalize recordOfUnion).members.length = 1
#guard (normalize (.prod (.union .nat .string) .unit)).members.length = 2
-- TY-10's positive control: a permuted record is raw-below its normal form.
#guard sub (.record [("b", false, .nat), ("a", false, .string)])
  (normalize (.record [("b", false, .nat), ("a", false, .string)]))
-- membership reads canonical order: the value carries the canonical names, in canonical order
#guard hasTy (.ctor 0 [.list [.str "a", .str "b"], .list [.str "x", .nat 1]])
  (.record [("b", false, .nat), ("a", false, .string)]) []
#guard hasTy (.ctor 0 [.list [.str "a", .str "b"], .list [.str "x", .nat 1]])
  (normalize (.record [("b", false, .nat), ("a", false, .string)])) []
#guard !hasTy (.ctor 0 [.list [.str "b", .str "a"], .list [.nat 1, .str "x"]])
  (.record [("b", false, .nat), ("a", false, .string)]) []
-- an optional key: absent from both lists, present, a present `none` at an option-typed field
#guard hasTy (.ctor 0 [.list [], .list []]) (.record [("a", true, .nat)]) []
#guard hasTy (.ctor 0 [.list [.str "a"], .list [.nat 3]]) (.record [("a", true, .nat)]) []
#guard !hasTy (.ctor 0 [.list [.str "a"], .list [.none]]) (.record [("a", true, .nat)]) []
#guard hasTy (.ctor 0 [.list [.str "a"], .list [.none]]) (.record [("a", true, .option .nat)]) []
#guard hasTy (.ctor 0 [.list [.str "b"], .list [.nat 2]]) (.record [("a", true, .nat), ("b", false, .nat)]) []
#guard !hasTy (.ctor 0 [.list [], .list []]) (.record [("a", false, .nat)]) []
-- width: an extra name, a repeated name, a missing required one: refused by the names
#guard !hasTy (.ctor 0 [.list [.str "a", .str "b"], .list [.nat 1, .nat 2]]) (.record [("a", false, .nat)]) []
#guard !hasTy (.ctor 0 [.list [.str "a", .str "a"], .list [.nat 1, .nat 2]]) (.record [("a", false, .nat), ("b", true, .nat)]) []
#guard !hasTy (.ctor 0 [.list [.str "a"], .list [.nat 1]]) (.record [("a", false, .nat), ("b", false, .nat)]) []
-- the union of two records rc.112 keeps apart: the one value fits one branch (row 165's case)
#guard hasTy (.ctor 0 [.list [.str "a", .str "b"], .list [.nat 1, .str "x"]])
  (.record [("a", false, .nat), ("b", false, .string)]) []
#guard !hasTy (.ctor 0 [.list [.str "a", .str "b"], .list [.nat 1, .str "x"]])
  (.record [("b", false, .nat), ("c", false, .string)]) []
-- a map: sorted distinct keys only
#guard hasTy (.list [.pair (.str "a") (.nat 1), .pair (.str "b") (.nat 2)]) (.map .string .nat) []
#guard !hasTy (.list [.pair (.str "b") (.nat 1), .pair (.str "a") (.nat 2)]) (.map .string .nat) []
#guard !hasTy (.list [.pair (.str "a") (.nat 1), .pair (.str "a") (.nat 2)]) (.map .string .nat) []
#guard hasTy (.list []) (.map .string .never) []
-- T's arms
#guard hasTy (.list [.nat 1, .str "a", .bool true]) (.tuple [.nat, .string, .bool]) []
#guard !hasTy (.list [.nat 1, .str "a"]) (.tuple [.nat, .string, .bool]) []
#guard hasTy (.list [.nat 1, .str "a"]) (.tuple [.nat, .string]) [] &&
  hasTy (.list [.nat 1, .str "a"]) (.prod .nat .string) []
#guard hasTy (.nat 3) .int [] && hasTy (.ctor 1 [.nat 0]) .int [] && hasTy (.nat 3) .number []
#guard hasTy (.ctor 2 [.bytes [0, 0, 0, 0, 0, 0, 248, 127]]) .number [] &&
  !hasTy (.ctor 2 [.bytes [0]]) .number [] && !hasTy (.ctor 2 [.bytes [0, 0, 0, 0, 0, 0, 248, 127]]) .int []
#guard hasTy .unit .undefined [] && hasTy .none .null [] && hasTy (.bytes [1, 2]) .bytes [] &&
  !hasTy .unit .null []

end ProbeP

#print axioms ProbeP.hasTy_record
#print axioms ProbeP.hasTy_tuple_pair
#print axioms ProbeP.hasTy_leafEdge
#print axioms ProbeP.hasTy_leafRule
#print axioms ProbeP.namedHasTy_mono
#print axioms ProbeP.itemsHasTy_mono
#print axioms ProbeP.hasTy_sub
#print axioms ProbeP.hasTy_members
#print axioms ProbeP.hasTy_normalizeRow
#print axioms ProbeP.hasTy_productMembers
#print axioms ProbeP.hasTy_normalize_record
#print axioms ProbeP.hasTy_normalize_tuple
#print axioms ProbeP.hasTy_normalize_app
#print axioms ProbeP.hasTy_normalize
#print axioms ProbeP.hasTy_join_left
#print axioms ProbeP.hasTy_join_right
#print axioms ProbeP.namedHasTy_names
#print axioms ProbeP.record_width_refused
#print axioms ProbeP.namedHasTy_absent
#print axioms ProbeP.record_required_below_optional
#print axioms ProbeP.record_sub_not_complete
#print axioms ProbeP.generated_int_image_breaks_tower
