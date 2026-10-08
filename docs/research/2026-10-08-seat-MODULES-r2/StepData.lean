import Effect4.Laws.Modules.Reading
import Effect4.Laws.Schema.Codec

/-! Probe MODS-9, after the review at 37c1dea4 (findings F1, F2 and F7).

The step language as first-order data:

- sorts, record schemas and field references are data; the syntax holds no function;
- each interpretation is a fold outside the syntax: the Lean meaning, the encoding, the term,
  the written fields and the JSON tree;
- a field's read and write are derived from the schema, never supplied by an author, and their
  record laws are proved once for every schema whose names are in canonical order;
- the frame law (a field that no update names keeps its value) is proved once, for the update
  spine of a record-sorted step;
- `Step.sound` holds for every well-formed step, from the input's reading alone. -/

set_option autoImplicit false

open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Modules
open Effect4.Store (Val)

namespace StepData

/-! ## The syntax: data only -/

/-- The sorts of the step language. A schema is a sort too, built from `nil` and `field`, and
`record` reads it. One inductive, so every fold reduces by structural recursion. -/
inductive Sy where
  | bool
  | nat
  | list (s : Sy)
  | pair (a b : Sy)
  | nil
  | field (name : String) (s : Sy) (rest : Sy)
  | record (fs : Sy)

/-- A schema: a sort built from `nil` and `field`. -/
abbrev Fields := Sy

/-- A field of a schema, by position: data. -/
inductive FieldRef : Sy → Sy → Type where
  | here (name : String) (s : Sy) (rest : Sy) : FieldRef (.field name s rest) s
  | there {name : String} {s' : Sy} {rest : Sy} {s : Sy} :
      FieldRef rest s → FieldRef (.field name s' rest) s

/-- The step language over one input of sort `ι`. -/
inductive Step (ι : Sy) : Sy → Type where
  | input : Step ι ι
  | bool (b : Bool) : Step ι .bool
  | ite {s : Sy} : Step ι .bool → Step ι s → Step ι s → Step ι s
  | pair {a b : Sy} : Step ι a → Step ι b → Step ι (.pair a b)
  | get {fs : Sy} {s : Sy} : Step ι (.record fs) → FieldRef fs s → Step ι s
  | set {fs : Sy} {s : Sy} : Step ι (.record fs) → FieldRef fs s → Step ι s →
      Step ι (.record fs)
  | emptyLike {s : Sy} : Step ι (.list s) → Step ι (.list s)

/-! ## Interpretations, outside the syntax -/

/-- The Lean meaning of a sort. -/
def Sy.I : Sy → Type
  | .bool => Bool
  | .nat => Nat
  | .list s => List s.I
  | .pair a b => a.I × b.I
  | .nil => Unit
  | .field _ s rest => s.I × rest.I
  | .record fs => fs.I

def Sy.names : Sy → List String
  | .field n _ rest => n :: Sy.names rest
  | _ => []

/-- The encoding of a value and, for a schema, its fields with their encoded values: one
structural fold, so both reduce. -/
def Sy.encE : (s : Sy) → s.I → Val × List (String × Val)
  | .bool, b => (.bool b, [])
  | .nat, n => (.nat n, [])
  | .list s, xs => (.list (xs.map fun y => (Sy.encE s y).1), [])
  | .pair a b, p => (Val.tuple [(Sy.encE a p.1).1, (Sy.encE b p.2).1], [])
  | .nil, _ => (.unit, [])
  | .field n s rest, x =>
    (Val.tuple [(Sy.encE s x.1).1, (Sy.encE rest x.2).1],
      (n, (Sy.encE s x.1).1) :: (Sy.encE rest x.2).2)
  | .record fs, x => (Machine.Record.frame (Sy.encE fs x).2, [])

/-- The encoding of a sort's values. A record is the machine's frame of all its fields. -/
def Sy.enc (s : Sy) (x : s.I) : Val := (s.encE x).1
/-- A schema's fields, each with its encoded value. -/
def Sy.entries (fs : Sy) (x : fs.I) : List (String × Val) := (Sy.encE fs x).2

def FieldRef.name {fs : Sy} {s : Sy} : FieldRef fs s → String
  | .here n _ _ => n
  | .there f => f.name

/-- The derived read of a field. -/
def FieldRef.get {fs : Sy} {s : Sy} : FieldRef fs s → fs.I → s.I
  | .here _ _ _, x => x.1
  | .there f, x => f.get x.2

/-- The derived write of a field: it changes that component and no other. -/
def FieldRef.set {fs : Sy} {s : Sy} : FieldRef fs s → fs.I → s.I → fs.I
  | .here _ _ _, x, v => (v, x.2)
  | .there f, x, v => (x.1, f.set x.2 v)

/-- A schema in canonical order: names strictly ascending by their bytes. -/
def Sy.Canonical (fs : Sy) : Prop :=
  fs.names.Pairwise (fun a b => Field.ltKey (Field.bytesKey a) (Field.bytesKey b) = true)

instance (fs : Sy) : Decidable fs.Canonical := by
  unfold Sy.Canonical; exact inferInstance

/-! ## The folds of a step -/

variable {ι : Sy}

def Step.term (src : TermSrc) : {s : Sy} → Step ι s → TermSrc
  | _, .input => src
  | _, .bool b => Authoring.bool b
  | _, .ite c t f => ifT (c.term src) (t.term src) (f.term src)
  | _, .pair a b => app "pair" [a.term src, b.term src]
  | _, .get r f => field (r.term src) f.name
  | _, .set r f v => recordSet (r.term src) f.name (v.term src)
  | _, .emptyLike xs => noneOf (xs.term src)

def Step.eval (v : ι.I) : {s : Sy} → Step ι s → s.I
  | _, .input => v
  | _, .bool b => b
  | _, .ite c t f => cond (c.eval v : Bool) (t.eval v) (f.eval v)
  | _, .pair a b => (a.eval v, b.eval v)
  | _, .get r f => f.get (r.eval v)
  | _, .set r f x => f.set (r.eval v) (x.eval v)
  | _, .emptyLike _ => []

def union (a b : List String) : List String := a ++ b.filter (fun x => decide (x ∉ a))

/-- The field names that a step's updates name: a conservative summary (finding F2). -/
def Step.writes : {s : Sy} → Step ι s → List String
  | _, .input => []
  | _, .bool _ => []
  | _, .ite c t f => union c.writes (union t.writes f.writes)
  | _, .pair a b => union a.writes b.writes
  | _, .get r _ => r.writes
  | _, .set r f x => union (union r.writes x.writes) [f.name]
  | _, .emptyLike xs => xs.writes

/-- The step as JSON, from the one tree (finding F7): no second interpretation. -/
def Step.json : {s : Sy} → Step ι s → Lean.Json
  | _, .input => .str "input"
  | _, .bool b => .bool b
  | _, .ite c t f => .mkObj [("if", c.json), ("then", t.json), ("else", f.json)]
  | _, .pair a b => .arr #[a.json, b.json]
  | _, .get r f => .mkObj [("get", .str f.name), ("of", r.json)]
  | _, .set r f x => .mkObj [("set", .str f.name), ("of", r.json), ("to", x.json)]
  | _, .emptyLike xs => .mkObj [("emptyLike", xs.json)]

/-- Every schema that a step reads or writes is canonical: a decidable check. -/
def Step.wf : {s : Sy} → Step ι s → Bool
  | _, .input => true
  | _, .bool _ => true
  | _, .ite c t f => c.wf && t.wf && f.wf
  | _, .pair a b => a.wf && b.wf
  | _, @Step.get _ fs _ r _ => decide fs.Canonical && r.wf
  | _, @Step.set _ fs _ r _ x => decide fs.Canonical && r.wf && x.wf
  | _, .emptyLike xs => xs.wf

/-! ## The record laws, once for every canonical schema -/

theorem entries_names : ∀ (fs : Sy) (x : fs.I), (fs.entries x).map Prod.fst = fs.names
  | .field n _ rest, x => by
    show ((n, Sy.enc _ x.1) :: Sy.entries rest x.2).map Prod.fst = n :: Sy.names rest
    rw [List.map_cons, entries_names rest x.2]
  | .bool, _ => rfl
  | .nat, _ => rfl
  | .list _, _ => rfl
  | .pair _ _, _ => rfl
  | .nil, _ => rfl
  | .record _, _ => rfl

theorem entries_ascending {fs : Sy} (h : fs.Canonical) (x : fs.I) :
    Field.Ascending Field.bytesKey (fs.entries x) := by
  unfold Field.Ascending
  unfold Sy.Canonical at h
  rw [← entries_names fs x, List.pairwise_map] at h
  exact h

theorem entries_nodup {fs : Sy} (h : fs.Canonical) (x : fs.I) :
    ((fs.entries x).map Prod.fst).Nodup :=
  Field.names_nodup_of_ascending (entries_ascending h x)

theorem name_mem : ∀ {fs s : Sy} (f : FieldRef fs s), f.name ∈ fs.names
  | _, _, .here _ _ _ => List.mem_cons_self
  | _, _, .there f => List.mem_cons_of_mem _ (name_mem f)

theorem get_mem : ∀ {fs s : Sy} (f : FieldRef fs s) (x : fs.I),
    (f.name, Sy.enc s (f.get x)) ∈ fs.entries x
  | _, _, .here m s rest, x =>
    show _ ∈ (m, Sy.enc s x.1) :: Sy.entries rest x.2 from List.mem_cons_self
  | _, _, @FieldRef.there m s' rest _ f, x =>
    show _ ∈ (m, Sy.enc s' x.1) :: Sy.entries rest x.2 from List.mem_cons_of_mem _ (get_mem f x.2)

/-- **The read law**, for every field of every canonical schema. -/
theorem read_law {fs s : Sy} (h : fs.Canonical) (f : FieldRef fs s) (x : fs.I) :
    Machine.Record.read false (Sy.enc (.record fs) x) f.name = some (Sy.enc s (f.get x)) := by
  have hf : Machine.Record.entries (Sy.enc (.record fs) x) = some (fs.entries x) :=
    Schema.Codec.entries_frame _ (entries_nodup h x)
  simp only [Machine.Record.read, Machine.Record.lookup, hf, Option.map_some,
    Field.firstOf_of_nodup (entries_nodup h x) (get_mem f x)]
  rfl

/-- What a write leaves at each name: the written value at its own name, the old elsewhere. -/
theorem firstOf_set : ∀ {fs s : Sy} (f : FieldRef fs s) (x : fs.I) (v : s.I)
    (_ : fs.names.Nodup) (n : String),
    Field.firstOf n (fs.entries (f.set x v)) =
      if f.name = n then some (Sy.enc s v) else Field.firstOf n (fs.entries x)
  | _, _, .here m s rest, x, v, _, n => by
    show Field.firstOf n ((m, Sy.enc s v) :: Sy.entries rest x.2) =
      if m = n then some (Sy.enc s v)
      else Field.firstOf n ((m, Sy.enc s x.1) :: Sy.entries rest x.2)
    simp only [Field.firstOf]
    by_cases hm : m = n
    · rw [if_pos hm, if_pos hm]
    · simp only [if_neg hm]
  | _, _, @FieldRef.there m s' rest s f, x, v, hnd, n => by
    show Field.firstOf n ((m, Sy.enc s' x.1) :: Sy.entries rest (f.set x.2 v)) =
      if f.name = n then some (Sy.enc s v)
      else Field.firstOf n ((m, Sy.enc s' x.1) :: Sy.entries rest x.2)
    have hnd' : m ∉ Sy.names rest ∧ (Sy.names rest).Nodup := List.nodup_cons.mp hnd
    simp only [Field.firstOf]
    by_cases hm : m = n
    · have hne : f.name ≠ n := fun e => hnd'.1 (hm ▸ e ▸ name_mem f)
      rw [if_pos hm, if_pos hm, if_neg hne]
    · rw [if_neg hm, if_neg hm, firstOf_set f x.2 v hnd'.2 n]

theorem names_set : ∀ {fs s : Sy} (f : FieldRef fs s) (x : fs.I) (v : s.I),
    (fs.entries (f.set x v)).map Prod.fst = fs.names := fun _ _ _ => entries_names _ _

/-- Two lists with distinct names and one `firstOf` at every name hold the same members. -/
theorem mem_iff_of_firstOf {l1 l2 : List (String × Val)} (h1 : (l1.map Prod.fst).Nodup)
    (h2 : (l2.map Prod.fst).Nodup) (h : ∀ n, Field.firstOf n l1 = Field.firstOf n l2) :
    ∀ p, p ∈ l1 ↔ p ∈ l2 := by
  intro p
  constructor
  · intro hp
    have := Field.firstOf_of_nodup h1 hp
    rw [h] at this
    exact Field.firstOf_mem this
  · intro hp
    have := Field.firstOf_of_nodup h2 hp
    rw [← h] at this
    exact Field.firstOf_mem this

/-- **The write law**, for every field of every canonical schema. -/
theorem write_law {fs s : Sy} (h : fs.Canonical) (f : FieldRef fs s) (x : fs.I) (v : s.I) :
    Machine.Record.set (Sy.enc (.record fs) x) f.name (Sy.enc s v) =
      some (Sy.enc (.record fs) (f.set x v)) := by
  have hf : Machine.Record.entries (Sy.enc (.record fs) x) = some (fs.entries x) :=
    Schema.Codec.entries_frame _ (entries_nodup h x)
  show (Machine.Record.entries (Sy.enc (.record fs) x)).bind (fun fields =>
      some (Machine.Record.frame (Field.canonBy Field.bytesKey ((f.name, Sy.enc s v) :: fields)))) =
    some (Machine.Record.frame (fs.entries (f.set x v)))
  rw [hf, Option.bind_some]
  have hnd : fs.names.Nodup := by
    rw [← entries_names fs x]; exact entries_nodup h x
  have hcanon := Field.canonBy_ascending (key := Field.bytesKey)
    ((f.name, Sy.enc s v) :: fs.entries x)
  have heq : Field.canonBy Field.bytesKey ((f.name, Sy.enc s v) :: fs.entries x) =
      fs.entries (f.set x v) := by
    apply Field.ascending_ext hcanon (entries_ascending h (f.set x v))
    apply mem_iff_of_firstOf (Field.names_nodup_of_ascending hcanon) (entries_nodup h _)
    intro n
    rw [Field.firstOf_canonBy Field.bytesKey_injective, firstOf_set f x v hnd n]
    simp only [Field.firstOf]
  rw [heq]

/-! ## Soundness, once for the language -/

/-- **Every well-formed step's term reads its model's value.** No law is supplied by an
author: the field laws come from the schema. -/
theorem Step.sound {src : TermSrc} {env : Env} {path : List Nat} {vals : List Val} {v : ι.I}
    (h : Reads src env path vals (Sy.enc ι v)) :
    {s : Sy} → (e : Step ι s) → e.wf = true → Reads (e.term src) env path vals (Sy.enc s (e.eval v))
  | _, .input, _ => h
  | _, .bool b, _ => reads_bool b _ _ _
  | _, .ite c t f, hw => by
    simp only [Step.wf, Bool.and_eq_true] at hw
    have w := reads_ifT (Step.sound h c hw.1.1) (Step.sound h t hw.1.2) (Step.sound h f hw.2)
    revert w
    simp only [Step.term, Step.eval]
    cases c.eval v <;> exact id
  | _, .pair a b, hw => by
    simp only [Step.wf, Bool.and_eq_true] at hw
    exact reads_pair (Step.sound h a hw.1) (Step.sound h b hw.2)
  | _, .get r f, hw => by
    simp only [Step.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
    exact reads_field (Step.sound h r hw.2) (read_law hw.1 f (r.eval v))
  | _, .set r f x, hw => by
    simp only [Step.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
    exact reads_recordSet (Step.sound h r hw.1.2) (Step.sound h x hw.2)
      (write_law hw.1.1 f (r.eval v) (x.eval v))
  | _, .emptyLike xs, hw => by
    simp only [Step.wf] at hw
    exact reads_noneOf (Step.sound h xs hw)

/-! ## The frame law, once: a field that no update names keeps its value -/

/-- The update spine of a record-sorted step: the input, a choice of two spines, or an update
of a spine. A field read that yields a record is not a spine, so it is outside the law. -/
def Step.spine : {s : Sy} → Step ι s → Bool
  | _, .input => true
  | _, .ite _ t f => t.spine && f.spine
  | _, .set r _ _ => r.spine
  | _, _ => false

theorem get_set_other : ∀ {fs : Sy} {s t : Sy} (f : FieldRef fs s) (g : FieldRef fs t)
    (x : fs.I) (v : s.I), fs.names.Nodup → f.name ≠ g.name → g.get (f.set x v) = g.get x
  | _, _, _, .here _ _ _, .here _ _ _, _, _, _, hne => absurd rfl hne
  | _, _, _, .here _ _ _, .there _, _, _, _, _ => rfl
  | _, _, _, .there _, .here _ _ _, _, _, _, _ => rfl
  | _, _, _, .there f, .there g, x, v, hnd, hne => by
    exact get_set_other f g x.2 v (List.nodup_cons.mp hnd).2 hne

theorem mem_union {n : String} {a b : List String} : n ∈ union a b ↔ n ∈ a ∨ n ∈ b := by
  simp only [union, List.mem_append, List.mem_filter]
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr h.1
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · by_cases ha : n ∈ a
      · exact Or.inl ha
      · exact Or.inr ⟨h, decide_eq_true ha⟩

/-- **The frame law**: on an update spine, a field that no update names keeps its value. -/
theorem frame_law {fs : Sy} {t : Sy} (hnd : fs.names.Nodup) (g : FieldRef fs t)
    (v : (Sy.record fs).I) :
    (e : Step (.record fs) (.record fs)) → e.spine = true → g.name ∉ e.writes →
      g.get (e.eval v) = g.get v
  | .input, _, _ => rfl
  | .ite c t f, hs, hw => by
    simp only [Step.spine, Bool.and_eq_true] at hs
    simp only [Step.writes, mem_union, not_or] at hw
    simp only [Step.eval]
    cases c.eval v
    · exact frame_law hnd g v f hs.2 hw.2.2
    · exact frame_law hnd g v t hs.1 hw.2.1
  | .set r f x, hs, hw => by
    simp only [Step.spine] at hs
    simp only [Step.writes, mem_union, not_or, List.mem_singleton] at hw
    simp only [Step.eval]
    rw [get_set_other f g (r.eval v) (x.eval v) hnd (fun e => hw.2 e.symm)]
    exact frame_law hnd g v r hs hw.1.1
  | .get _ _, hs, _ => by
    simp only [Step.spine] at hs
    exact absurd hs (by decide)

end StepData

/-! ## Latch's cell and steps, written as data -/

namespace StepData

/-- A waiter: two identities, here numbers. Names in canonical order. -/
def waiterS : Sy := .field "hint" .nat (.field "id" .nat .nil)
/-- Latch's cell: `open` precedes `waiters` by bytes. -/
def cellS : Sy := .field "open" .bool (.field "waiters" (.list (.record waiterS)) .nil)
def openF : FieldRef cellS .bool := .here _ _ _
def waitersF : FieldRef cellS (.list (.record waiterS)) := .there (.here _ _ _)

abbrev Cell := Step (.record cellS)

/-- `release`: the reply (whether it was closed, the woken), and the next cell. -/
def releaseD : Cell (.pair (.pair .bool (.list (.record waiterS))) (.record cellS)) :=
  .ite (.get .input openF)
    (.pair (.pair (.bool false) (.emptyLike (.get .input waitersF))) .input)
    (.pair (.pair (.bool true) (.get .input waitersF))
      (.set .input waitersF (.emptyLike (.get .input waitersF))))

/-- `release`'s next cell alone: an update spine. -/
def releaseNext : Cell (.record cellS) :=
  .ite (.get .input openF) .input (.set .input waitersF (.emptyLike (.get .input waitersF)))

/-- The fault "release opens", as data. -/
def releaseOpensNext : Cell (.record cellS) :=
  .ite (.get .input openF) .input
    (.set (.set .input waitersF (.emptyLike (.get .input waitersF))) openF (.bool true))

#guard decide cellS.Canonical && decide waiterS.Canonical
#guard releaseD.wf && releaseNext.wf && releaseOpensNext.wf
#guard releaseNext.spine && releaseOpensNext.spine
#guard releaseD.writes == ["waiters"]
#guard releaseOpensNext.writes == ["waiters", "open"]
-- The term is MODS-1's hand term, with `pair` for the inner reply.
#guard releaseD.term (var "s") { names := ["s"] } [] ==
  (ifT (field (var "s") "open")
    (app "pair" [app "pair" [bool false, noneOf (field (var "s") "waiters")], var "s"])
    (app "pair" [app "pair" [bool true, field (var "s") "waiters"],
      recordSet (var "s") "waiters" (noneOf (field (var "s") "waiters"))])) { names := ["s"] } []
#eval releaseD.json.compress

/-- The frame law at Latch: a release keeps `open`, with no proof of its own. -/
example (v : (Sy.record cellS).I) : openF.get (releaseNext.eval v) = openF.get v :=
  frame_law (by decide) openF v releaseNext rfl (by decide)

-- The fault names `open`, so the frame law does not apply to it: a red control.
#guard releaseOpensNext.writes.contains openF.name

/-- Soundness at Latch: from the language's one theorem. -/
example (v : (Sy.record cellS).I) {src : TermSrc} {env : Env} {path : List Nat}
    {vals : List Val} (h : Reads src env path vals (Sy.enc _ v)) :
    Reads (releaseD.term src) env path vals (Sy.enc _ (releaseD.eval v)) :=
  Step.sound h releaseD rfl

end StepData

#print axioms StepData.Step.sound
#print axioms StepData.read_law
#print axioms StepData.write_law
#print axioms StepData.frame_law
