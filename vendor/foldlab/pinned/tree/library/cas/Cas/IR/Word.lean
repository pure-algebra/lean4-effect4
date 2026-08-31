import Cas.Core.Store

/-!
# The store word — the IR

The executable carrier of the language: bindings in children-first
admission order. The grammar's `flatten` emits it, the interpreter
threads it, the vector lane serializes it, and `toStore` projects it
onto the function store the theorem corpus quantifies over.

The word is not an implementation convenience standing in for the
store: the order IS semantics. Children-first is the admission
discipline (`wf` — every reference resolves among strictly earlier
bindings, at its declared kind), the transfer order of the push
composite, and the upload order the TypeScript `Graph.closure` emits.
A serialized word is a replayable admission history, which is exactly
what a conformance vector is.

Resolution is first-binding (`find`), `toStore` is definitionally
`find`, and the bridge theorem carries the weight: a word that passes
`wf` projects to a `Closed` store (`wf_toStore_closed`) — nothing
dangles, nothing mis-kinds, through the word as through the store.
-/

namespace Cas

/-- One address-to-node binding. Naming the fields prevents the address
and node from becoming anonymous tuple positions at every boundary. -/
structure Binding where
  address : Addr32
  node : Node
  deriving DecidableEq

/-- The store word: bindings in admission order, earliest first. -/
abbrev Word := List Binding

/-- A word with at least one binding. This is the carrier for values
whose semantics require a final/root binding. -/
structure NonemptyWord where
  word : Word
  nonempty : word ≠ []

namespace NonemptyWord

/-- The final binding, total because the word is non-empty. -/
def root (w : NonemptyWord) : Binding :=
  w.word.getLast w.nonempty

def length (w : NonemptyWord) : Nat := w.word.length

end NonemptyWord

namespace Word

/-- First-binding resolution. -/
def find : Word → Addr32 → Option Node
  | [], _ => none
  | ⟨a, n⟩ :: rest, b => if b = a then some n else find rest b

@[simp] theorem find_nil (a : Addr32) : find [] a = none := rfl

theorem find_append_of_some {w : Word} {a : Addr32} {n : Node} (v : Word)
    (h : find w a = some n) : find (w ++ v) a = some n := by
  induction w with
  | nil => simp at h
  | cons e rest ih =>
    obtain ⟨b, m⟩ := e
    by_cases hab : a = b
    · simpa [find, hab] using h
    · simp only [find, if_neg hab] at h
      simpa [find, hab] using ih h

theorem find_append_of_none {w : Word} {a : Addr32} (v : Word)
    (h : find w a = none) : find (w ++ v) a = find v a := by
  induction w with
  | nil => simp
  | cons e rest ih =>
    obtain ⟨b, m⟩ := e
    by_cases hab : a = b
    · simp [find, hab] at h
    · simp only [find, if_neg hab] at h
      simpa [find, hab] using ih h

/-- A found binding is a member. -/
theorem find_mem {w : Word} {a : Addr32} {n : Node}
    (h : find w a = some n) : Binding.mk a n ∈ w := by
  induction w with
  | nil => simp at h
  | cons e rest ih =>
    obtain ⟨b, m⟩ := e
    by_cases hab : a = b
    · simp only [find, if_pos hab] at h
      injection h with h
      simp [hab, h]
    · simp only [find, if_neg hab] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- A member's address always resolves to something. -/
theorem find_isSome_of_mem {w : Word} {a : Addr32} {n : Node}
    (h : Binding.mk a n ∈ w) : (find w a).isSome := by
  induction w with
  | nil => simp at h
  | cons e rest ih =>
    obtain ⟨b, m⟩ := e
    by_cases hab : a = b
    · simp [find, hab]
    · rcases List.mem_cons.mp h with heq | hmem
      · exact absurd (congrArg Binding.address heq) hab
      · simpa [find, hab] using ih hmem

/-- A reference resolves in a word when its first binding carries the
declared kind tag. -/
def resolvesIn (w : Word) (r : Ref) : Bool :=
  match find w r.addr with
  | some n => n.tag == r.expectedTag
  | none => false

theorem resolvesIn_iff {w : Word} {r : Ref} :
    resolvesIn w r = true ↔
      ∃ m, find w r.addr = some m ∧ m.tag = r.expectedTag := by
  unfold resolvesIn
  cases h : find w r.addr with
  | none => simp
  | some m =>
    constructor
    · intro hb
      exact ⟨m, rfl, beq_iff_eq.mp hb⟩
    · rintro ⟨m', hm', ht⟩
      injection hm' with he
      subst he
      exact beq_iff_eq.mpr ht

/-- Resolution is monotone: growing the word never invalidates a
passed reference check — the lock-free reading of grow-only. -/
theorem resolvesIn_mono {w : Word} (v : Word) {r : Ref}
    (h : resolvesIn w r = true) : resolvesIn (w ++ v) r = true := by
  rcases resolvesIn_iff.mp h with ⟨m, hm, ht⟩
  exact resolvesIn_iff.mpr ⟨m, find_append_of_some v hm, ht⟩

/-- The admission scan, with the already-admitted prefix explicit. -/
def wfFrom (prior : Word) : Word → Bool
  | [] => true
  | ⟨a, n⟩ :: rest =>
    n.refs.all (resolvesIn prior) &&
      wfFrom (prior ++ [Binding.mk a n]) rest

/-- Admission over a word: every binding's references resolve among
strictly earlier bindings, at their declared kinds — closure, kind
discipline, and acyclicity in one executable predicate. -/
def wf (w : Word) : Bool := wfFrom [] w

theorem wfFrom_append (prior x y : Word) :
    wfFrom prior (x ++ y)
      = (wfFrom prior x && wfFrom (prior ++ x) y) := by
  induction x generalizing prior with
  | nil => simp [wfFrom]
  | cons e rest ih =>
    obtain ⟨a, n⟩ := e
    simp only [List.cons_append, wfFrom, ih, Bool.and_assoc,
      List.append_assoc, List.nil_append]

/-- Interior of the bridge: a prefix whose bindings already resolve
stays resolved while the scan admits the rest. -/
theorem wfFrom_resolves {prior rest : Word}
    (hprior : ∀ a n, find prior a = some n →
      ∀ r ∈ n.refs, resolvesIn prior r = true)
    (h : wfFrom prior rest = true) :
    ∀ a n, find (prior ++ rest) a = some n →
      ∀ r ∈ n.refs, resolvesIn (prior ++ rest) r = true := by
  induction rest generalizing prior with
  | nil =>
    intro a n hf r hr
    rw [List.append_nil] at hf ⊢
    exact hprior a n hf r hr
  | cons e rest ih =>
    obtain ⟨b, m⟩ := e
    simp only [wfFrom, Bool.and_eq_true] at h
    obtain ⟨hrefs, hrest⟩ := h
    have hassoc : prior ++ Binding.mk b m :: rest =
        (prior ++ [Binding.mk b m]) ++ rest := by
      simp
    rw [hassoc]
    refine ih ?_ hrest
    intro a n hf r hr
    cases hp : find prior a with
    | some n' =>
      rw [find_append_of_some _ hp] at hf
      injection hf with he
      subst he
      exact resolvesIn_mono _ (hprior a n' hp r hr)
    | none =>
      rw [find_append_of_none _ hp] at hf
      by_cases hab : a = b
      · simp only [find, if_pos hab] at hf
        injection hf with he
        subst he
        exact resolvesIn_mono _ (List.all_eq_true.mp hrefs r hr)
      · simp [find, hab] at hf

/-- The store word projected onto the function store. -/
def toStore (w : Word) : Store := fun a => find w a

/-- The bridge (ledger L1): a word that passes `wf` projects to a
closed store. The two impossible states of the resident graph —
dangling and mis-kinded references — are impossible through the word
exactly as through the store. -/
theorem wf_toStore_closed {w : Word} (h : wf w = true) :
    Store.Closed (toStore w) := by
  intro a n hf r hr
  have hf' : find w a = some n := hf
  have base : ∀ a n, find ([] : Word) a = some n →
      ∀ r ∈ n.refs, resolvesIn [] r = true := by
    intro a n hf
    simp at hf
  have main := wfFrom_resolves base h a n (by simpa using hf') r hr
  have main' : resolvesIn w r = true := by simpa using main
  rcases resolvesIn_iff.mp main' with ⟨m, hm, ht⟩
  exact ⟨m, hm, ht⟩

/-- A proof-bearing admitted word for formal paths. Concrete digest
fixtures use the checked runtime boundary instead, because no digest
injectivity premise is assumed for SHA-256. -/
structure Admitted where
  word : NonemptyWord
  wf : Word.wf word.word = true

namespace Admitted

def toStore (w : Admitted) : Store := Word.toStore w.word.word

theorem closed (w : Admitted) : Store.Closed w.toStore :=
  Word.wf_toStore_closed w.wf

end Admitted

/-- Admitting one binding whose references resolve preserves `wf` —
the word face of `put_fresh_closed`. -/
theorem wf_snoc {w : Word} {a : Addr32} {n : Node}
    (hw : wf w = true) (hrefs : ∀ r ∈ n.refs, resolvesIn w r = true) :
    wf (w ++ [Binding.mk a n]) = true := by
  unfold wf at hw ⊢
  rw [wfFrom_append, List.nil_append]
  simp only [Bool.and_eq_true]
  refine ⟨hw, ?_⟩
  simp only [wfFrom, Bool.and_true, List.all_eq_true]
  exact fun r hr => hrefs r hr

/-- F2, shadowing half (Level 0): appending at an occupied address is
invisible through the bridge — first-binding resolution makes the
second binding inert, which is the word face of `put`'s duplicate
being a no-op. -/
theorem toStore_append_shadowed {w : Word} {a : Addr32}
    (h : (find w a).isSome) (m : Node) :
    toStore (w ++ [Binding.mk a m]) = toStore w := by
  funext b
  show find (w ++ [Binding.mk a m]) b = find w b
  cases hf : find w b with
  | some n => rw [find_append_of_some _ hf]
  | none =>
    rw [find_append_of_none _ hf]
    by_cases hb : b = a
    · subst hb
      rw [hf] at h
      exact absurd h (by simp)
    · simp [find, hb]

/-- The bridge respects store-equal prefixes: growing two words that
project to one store by the same suffix keeps them projecting to one
store. -/
theorem toStore_append_congr {w w' : Word}
    (h : toStore w = toStore w') (v : Word) :
    toStore (w ++ v) = toStore (w' ++ v) := by
  funext b
  have hb : find w b = find w' b := congrFun h b
  show find (w ++ v) b = find (w' ++ v) b
  cases hf : find w b with
  | some n =>
    rw [find_append_of_some v hf, find_append_of_some v (hb.symm.trans hf)]
  | none =>
    rw [find_append_of_none v hf, find_append_of_none v (hb.symm.trans hf)]

/-- Appending at a fresh address is `Store.set` through the bridge. -/
theorem toStore_snoc {w : Word} {a : Addr32} (n : Node)
    (h : find w a = none) :
    toStore (w ++ [Binding.mk a n]) = (toStore w).set a n := by
  funext b
  by_cases hb : b = a
  · subst hb
    simp [toStore, Store.set, find_append_of_none _ h, find]
  · simp only [toStore, Store.set, if_neg hb]
    cases hf : find w b with
    | some m => rw [find_append_of_some _ hf]
    | none =>
      rw [find_append_of_none _ hf]
      simp [find, hb]

end Word

end Cas
