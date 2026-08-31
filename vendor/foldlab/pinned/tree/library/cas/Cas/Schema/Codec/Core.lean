import Cas.Schema.Codec.Scalars
import Cas.Schema.Codec.References

/-!
# Generic schema codec

The mutually recursive encoder and strict canonical-image decoder, plus
the emitted-field-key fact needed by the optional-field branch.
-/

namespace Cas.Schema

/-! ## The generic codec -/

mutual

/-- Structural on the code, so it reduces definitionally — the same
shape as the canonical printers. -/
def encode : (a : Ast) → El a → Json.Value
  | .null, _ => .null
  | .bool, b => .bool b
  | .int, i => encInt i
  | .str, s => .str s
  | .lit l, _ => encLit l
  | .arr a, xs => .arr (xs.map (encode a))
  | .struct fs, x => .obj (encodeFields fs x)
  | .ref t, r => encRef t r.addr
  | .union ms _, x => encodeMembers (discriminatedB ms) ms x

def encodeFields :
    (fs : List (String × Bool × Ast)) → ElFields fs →
      List (String × Json.Value)
  | [], _ => []
  | (n, true, a) :: fs, (x, rest) =>
    (match x with
      | some v => [(n, encode a v)]
      | none => []) ++ encodeFields fs rest
  | (n, false, a) :: fs, (v, rest) =>
    (n, encode a v) :: encodeFields fs rest

/-- A union member's value encodes as that member's value, plainly: the
sum tells us WHICH member, and the member's own encoding already
carries the `_tag` field that tells the decoder the same thing. No
wrapper, no envelope — the wire shape of a tagged union is the wire
shape of the member that matched, which is exactly Effect's.

The discrimination bit is an explicit argument rather than a guard
inside the body: `El (.union ms m)` is `cond (discriminatedB ms) …` by
definition, so instantiating `b` at `discriminatedB ms` makes the union
arm typecheck with no cast, and the `false` arm is the honest
`Empty.elim` the undiscriminated case has always been. -/
def encodeMembers :
    (b : Bool) → (ms : List Ast) → cond b (ElMembers ms) Empty →
      Json.Value
  | true, [], x => Empty.elim x
  | true, [a], x => encode a x
  | true, a :: b :: rest, x =>
    match x with
    | Sum.inl y => encode a y
    | Sum.inr y => encodeMembers true (b :: rest) y
  | false, _, x => Empty.elim x

end

mutual

def decode : (a : Ast) → Json.Value → Option (El a)
  | .null, .null => some ()
  | .bool, .bool b => some b
  | .int, v => decInt v
  | .str, .str s => some s
  | .lit .null, .null => some ()
  | .lit (.bool b), .bool b' => if b' = b then some () else none
  | .lit (.int i), v =>
    (decInt v).bind fun j => if j = i then some () else none
  | .lit (.str s), .str s' => if s' = s then some () else none
  | .arr a, .arr vs => decodeList a vs
  | .struct fs, .obj kvs => decodeFields fs kvs
  | .ref t, v => (decRef t v).map (fun a => StoreRef.mk a)
  | .union ms _, v => decodeMembers (discriminatedB ms) ms v
  | _, _ => none
termination_by a v => (sizeOf v, sizeOf a)

def decodeList : (a : Ast) → List Json.Value → Option (List (El a))
  | _, [] => some []
  | a, v :: vs =>
    (decode a v).bind fun x =>
    (decodeList a vs).bind fun xs =>
    some (x :: xs)
termination_by a vs => (sizeOf vs, sizeOf a)

def decodeFields :
    (fs : List (String × Bool × Ast)) → List (String × Json.Value) →
      Option (ElFields fs)
  | [], [] => some ()
  | [], _ :: _ => none
  | (_, true, _) :: fs, [] =>
    (decodeFields fs []).bind fun rest => some (none, rest)
  | (_, false, _) :: _, [] => none
  | (n, true, a) :: fs, (k, v) :: kvs =>
    if k = n then
      (decode a v).bind fun x =>
      (decodeFields fs kvs).bind fun rest =>
      some (some x, rest)
    else
      (decodeFields fs ((k, v) :: kvs)).bind fun rest => some (none, rest)
  | (n, false, a) :: fs, (k, v) :: kvs =>
    if k = n then
      (decode a v).bind fun x =>
      (decodeFields fs kvs).bind fun rest =>
      some (x, rest)
    else none
termination_by fs kvs => (sizeOf kvs, sizeOf fs)

/-- Tag dispatch, spelled as try-in-order. Under discrimination the two
readings coincide — at most one member can accept a value, because the
members' `_tag` literals are pairwise distinct — so this decoder is
deterministic in the value rather than in the order, and the round trip
is a theorem (`decodeMembers_encodeMembers`) rather than a hope.

Written with `Option.or` and not a nested match on purpose: one
functional-induction case per arm, and the success/failure split is
done by hand in the proofs, the way `decodeList` already does it with
`bind`. -/
def decodeMembers :
    (b : Bool) → (ms : List Ast) → Json.Value →
      Option (cond b (ElMembers ms) Empty)
  | true, [], _ => none
  | true, [a], v => decode a v
  | true, a :: b :: rest, v =>
    ((decode a v).map Sum.inl).or
      ((decodeMembers true (b :: rest) v).map Sum.inr)
  | false, _, _ => none
termination_by _b ms v => (sizeOf v, sizeOf ms)

end

/-! ## Emitted keys come from the code — what the skip branch needs -/

theorem encodeFields_keys :
    ∀ (fs : List (String × Bool × Ast)) (x : ElFields fs),
      ∀ k ∈ (encodeFields fs x).map (·.1), k ∈ fs.map (fun f => f.1) := by
  intro fs
  induction fs with
  | nil => intro x k hk; simp [encodeFields] at hk
  | cons f fs ih =>
    obtain ⟨n, opt, a⟩ := f
    intro x k hk
    cases opt with
    | true =>
      obtain ⟨xv, rest⟩ := x
      cases xv with
      | some v =>
        simp only [encodeFields, List.map_append, List.mem_append,
          List.map_cons, List.mem_cons, List.map_nil] at hk
        rcases hk with hk | hk
        · simp at hk
          simp [hk]
        · simpa using Or.inr (ih rest k hk)
      | none =>
        simp only [encodeFields, List.nil_append] at hk
        simpa using Or.inr (ih rest k hk)
    | false =>
      obtain ⟨v, rest⟩ := x
      simp only [encodeFields, List.map_cons, List.mem_cons] at hk
      rcases hk with hk | hk
      · simp [hk]
      · simpa using Or.inr (ih rest k hk)

/-! ## The tag is visible in the bytes — what tag dispatch needs

Two facts about the encode image, and the whole discriminated-union
argument rests on them: a tagged member encodes with its `_tag` literal
at the HEAD of the object, and a member sum's encoding therefore
carries one of the list's own tags at that head. Distinct tags then
make the members' images disjoint, which is exactly why the union round
trip is a theorem. -/

/-- A tagged member's encoding leads with its tag, verbatim. -/
theorem encode_memberTag {a : Ast} {t : String} (h : memberTag a = some t) :
    ∀ (x : El a), ∃ kvs, encode a x = .obj ((tagField, .str t) :: kvs) := by
  obtain ⟨fs, rfl⟩ := memberTag_eq h
  intro x
  obtain ⟨v, rest⟩ := x
  exact ⟨encodeFields fs rest, by simp only [encode, encodeFields, encLit]⟩

/-- A discriminated member sum's encoding leads with one of the list's
own tags. -/
theorem encodeMembers_tag :
    ∀ (ms : List Ast), discriminatedB ms = true →
      ∀ (x : cond true (ElMembers ms) Empty),
        ∃ t, t ∈ tagsOf ms ∧ ∃ kvs,
          encodeMembers true ms x = .obj ((tagField, .str t) :: kvs)
  | [], _, x => Empty.elim x
  | [a], h, x => by
    obtain ⟨t, ht, _⟩ := discriminatedB_head h
    obtain ⟨kvs, he⟩ := encode_memberTag ht x
    exact ⟨t, mem_tagsOf (by simp) ht, kvs, he⟩
  | a :: b :: rest, h, x => by
    match x with
    | Sum.inl y =>
      obtain ⟨t, ht, _⟩ := discriminatedB_head h
      obtain ⟨kvs, he⟩ := encode_memberTag ht y
      exact ⟨t, mem_tagsOf (by simp) ht, kvs, he⟩
    | Sum.inr y =>
      obtain ⟨t, hmem, kvs, he⟩ :=
        encodeMembers_tag (b :: rest) (discriminatedB_tail h) y
      exact ⟨t, tagsOf_cons_mem a hmem, kvs, he⟩

end Cas.Schema

