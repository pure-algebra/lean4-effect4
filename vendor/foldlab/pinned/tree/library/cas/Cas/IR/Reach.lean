import Cas.IR.Word

/-!
# Reachability over the word — the product's core gesture, given a carrier

"Everything about X" is the question the store exists to answer, and
until this module the model had no relation to answer it with:
references live in nodes, and only the HOST walked them. This is that
walk, stated.

## The edge reads the RESOLVED occurrence, and that is forced

A word may bind one address twice. `find` answers with the FIRST
binding, `toStore` is definitionally `find`, and `toStore_append_shadowed`
says the later binding is invisible through the bridge. So there are
two candidate edges out of an address: one per binding OCCURRENCE, or
one from the occurrence the store actually resolves. `Edge` takes the
second, and the reason is not taste — it is what `wf` quantifies over.

`wf` checks EVERY occurrence: at each position, that binding's
references must resolve among the bindings strictly before it. Read as
an occurrence relation, that check does NOT force a backward edge in
first-occurrence order, and the headline results below are FALSE. The
witness is three bindings:

```text
w = [ ⟨a, n₀⟩ , ⟨b, m⟩ , ⟨a, n₁⟩ ]      n₀, m without references
                                         m references a   (resolves in [⟨a,n₀⟩])
                                         n₁ references b  (resolves in [⟨a,n₀⟩,⟨b,m⟩])
```

Every occurrence's references resolve strictly earlier, so `wf w` holds
— yet the occurrence relation carries `a → b` (from the SECOND binding
at `a`) and `b → a`, a two-cycle between distinct addresses. Acyclicity
and the topological statement both fail, and no premise available on a
grow-only word rescues them.

Under the resolved reading the same word carries only `b → a`: the
second binding at `a` is inert, exactly as the store says it is, and
`n₁`'s references are checked but belong to a node no query can see.
The relation this module defines is the RESIDENT graph — the one
`Store.Closed` is about (`wf_toStore_closed`) — and it is acyclic
because `find` resolves first and `wf` resolves strictly earlier.

**The witness is data, not prose.** `shadowedWord` below is that word as
Lean values, `shadowedWord_wf` COMPUTES its admission, and four
theorems exhibit the fork: `edgeOccurrence` carries both directions
(`occurrence_two_cycle`), `Edge` carries one (`edge_shadowed_ba`,
`not_edge_shadowed_ab`). A reader who doubts the cut can re-run it
rather than re-derive it, and a future edit that quietly restores the
occurrence reading fails a build instead of a review.

## The index is the first-occurrence index, for the same reason

`firstIndex w a` is the position of the binding `find` answers with,
and `w.length` when the word does not bind the address at all. It is
the honest index against shadowing precisely because it indexes the
occurrence the edge was read from; indexing a later occurrence would
index a node the store does not hold.

## The direction, and the theorem that is ours

`wf_edge_index` says an edge moves STRICTLY DOWN this index: if the
resident node at `a` references `b`, then `b`'s first binding stands
strictly before `a`'s. Admission order is therefore a topological sort
of the reference graph — the direction is fixed by `resolvesIn`'s own
quantification (`wfFrom` hands each binding the prefix BEFORE it, never
the whole word), not chosen. `reach_acyclic` falls out: a cycle would
need the index to strictly decrease around a loop.

## The correspondence (banked reader lane, 2026-08-30)

`Reach` mirrors `Relation.ReflTransGen`'s exact two-constructor shape —
`refl`, and `tail : ReflTransGen r a b → r b c → ReflTransGen r a c` —
restated in-tree because the tower imports nothing. `Reach.single`,
`Reach.trans` and `reach_mono` are that API's `single`, `trans` and
`mono`.

Beyond the closure itself the reader found NOTHING to import, and the
absence is the interesting half. Mathlib carries no `Decidable`
instance for `ReflTransGen` or `TransGen`; `Digraph` has no path,
reachability or acyclicity API at all; `Quiver.Path` has no acyclicity;
and the only topological-order content in the library is Szpilrajn's
`extend_partialOrder`, an existence proof by Zorn that says nothing
about lists. So this module is NOVEL TERRITORY rather than a
re-spelling: `edgeB` decides one step of a closure Mathlib decides no
step of, `wf_edge_index` is the theorem the library has no counterpart
for, and `reachB` decides the closure itself — sound on any word
(`reachB_sound`), complete on an admitted one (`reachB_complete`).

The decision is not a fuel parameter someone picked. `wf_edge_index`
IS the termination measure: every edge strictly descends the admission
index, so a path out of `a` is shorter than `firstIndex w a`, and
running the search at the word's own length is therefore exhaustive.
Decidability of reachability here is a CONSEQUENCE of admission, which
is the same sentence as "admission order is a topological sort" read
computationally.

owed(reach-search-memoized): `reachIn` re-explores shared subgraphs, so
the search is exponential in the word's length where a visited-set walk
would be linear in the edges. Nothing above depends on the cost — the
model states the relation and the host computes it — but a version that
carries a frontier, and the agreement theorem tying it to `reachB`, is
a slice of its own.
-/

namespace Cas

namespace Word

/-! ## The edge -/

/-- The reference edge of the RESIDENT graph: the node the store
resolves at `a` carries a reference to `b`. The resolution is `find`'s
— first binding — so a shadowed later binding contributes no edge, in
step with `toStore_append_shadowed` making it invisible through the
bridge. -/
def Edge (w : Word) (a b : Addr32) : Prop :=
  ∃ n, find w a = some n ∧ ∃ r ∈ n.refs, r.addr = b

/-- The edge, decided. `find` is a scan and a node's references are a
list, so one step of the walk is a `Bool` computation with no premise
at all — which is already more than Mathlib offers for any closure it
defines. -/
def edgeB (w : Word) (a b : Addr32) : Bool :=
  match find w a with
  | some n => n.refs.any (fun r => decide (r.addr = b))
  | none => false

/-- The computation decides the relation, on any word and with no
premise. -/
theorem edgeB_iff {w : Word} {a b : Addr32} : edgeB w a b = true ↔ Edge w a b := by
  unfold edgeB Edge
  cases hf : find w a with
  | none => simp
  | some n => simp

/-- One step of the reference walk is decidable outright, so it is
carried as an instance. The CLOSURE's decision is the premise-bearing
`decidableReach` below, and the difference between the two is the whole
subject of this module. -/
instance instDecidableEdge (w : Word) (a b : Addr32) : Decidable (Edge w a b) :=
  decidable_of_iff (edgeB w a b = true) edgeB_iff

/-- Growth never removes an edge: `find` answers the same wherever the
word grows behind it. No admission premise is needed — this is the
grow-only law read one level up. -/
theorem edge_mono {w : Word} (v : Word) {a b : Addr32} (h : Edge w a b) :
    Edge (w ++ v) a b := by
  obtain ⟨n, hf, r, hr, hrb⟩ := h
  exact ⟨n, find_append_of_some v hf, r, hr, hrb⟩

/-! ## The refutation, mechanized

The module docstring argues that reading the edge off every binding
OCCURRENCE makes `wf_edge_index` and `reach_acyclic` false. This section
is that argument as Lean values and computations rather than as a
paragraph, which is what makes it survive an edit nobody re-reads.

The shape is three bindings over two addresses, with the FIRST address
bound twice: the late binding's references resolve (everything they name
stands strictly before them, so `wf` admits the word) while the node
they belong to is invisible through `find`. That gap — checked by `wf`,
unreachable through `find` — is the whole phenomenon. -/

/-- The shadowed address: bound first with no references, and again at
the end with a reference the store never resolves. -/
def shadowedA : Addr32 := ⟨List.replicate 32 0, by simp⟩

/-- The middle address, bound once. -/
def shadowedB : Addr32 := ⟨List.replicate 32 1, by simp⟩

/-- Distinct, so the cycle below is a genuine two-cycle and not a
self-loop wearing two names. -/
theorem shadowedA_ne_shadowedB : shadowedA ≠ shadowedB := by decide

/-- The resident node at `shadowedA`: no references at all, which is why
the resolved reading has no edge out of `shadowedA`. -/
def shadowedFirst : Node := ⟨0, 10, [], []⟩

/-- The node at `shadowedB`, referencing `shadowedA` — one edge, under
either reading. -/
def shadowedMid : Node := ⟨0, 20, [], [⟨10, shadowedA⟩]⟩

/-- The SECOND node at `shadowedA`, referencing `shadowedB`. Admitted,
because `shadowedB` stands strictly before it; invisible, because `find`
already answered at `shadowedA`. -/
def shadowedLate : Node := ⟨0, 30, [], [⟨20, shadowedB⟩]⟩

/-- The witness word: `shadowedA`, `shadowedB`, then `shadowedA` again.
-/
def shadowedWord : Word :=
  [⟨shadowedA, shadowedFirst⟩, ⟨shadowedB, shadowedMid⟩,
    ⟨shadowedA, shadowedLate⟩]

/-- The word is ADMITTED — computed, not assumed. Everything the
refutation says rests on this: no premise available on a grow-only word
excludes it, because the word passes the estate's own admission scan. -/
theorem shadowedWord_wf : wf shadowedWord = true := by decide

/-- THE READING THIS MODULE REFUSES: an edge off every binding
OCCURRENCE, which is the naive match to `wf`'s own quantification. It is
defined here only to be refuted, and nothing else in the library uses
it. -/
def edgeOccurrence (w : Word) (a b : Addr32) : Prop :=
  ∃ n, Binding.mk a n ∈ w ∧ ∃ r ∈ n.refs, r.addr = b

/-- THE REFUTATION: on an ADMITTED word, the occurrence reading carries a
two-cycle between distinct addresses. `reach_acyclic` and
`wf_edge_index` are therefore FALSE under it — the cut to the resolved
reading is forced, not preferred. -/
theorem occurrence_two_cycle :
    ∃ (w : Word) (a b : Addr32), wf w = true ∧ a ≠ b ∧
      edgeOccurrence w a b ∧ edgeOccurrence w b a :=
  ⟨shadowedWord, shadowedA, shadowedB, shadowedWord_wf, shadowedA_ne_shadowedB,
    ⟨shadowedLate, by decide, ⟨20, shadowedB⟩, by decide, rfl⟩,
    ⟨shadowedMid, by decide, ⟨10, shadowedA⟩, by decide, rfl⟩⟩

/-- The resolved reading on the same word: the edge out of `shadowedB`
survives, because `shadowedMid` is what `find` answers there. -/
theorem edge_shadowed_ba : Edge shadowedWord shadowedB shadowedA :=
  ⟨shadowedMid, by decide, ⟨10, shadowedA⟩, by decide, rfl⟩

/-- And the edge that closed the cycle is GONE: `find` answers
`shadowedFirst` at `shadowedA`, and `shadowedFirst` references nothing.
The two theorems together are the cut, exhibited on one word. -/
theorem not_edge_shadowed_ab : ¬ Edge shadowedWord shadowedA shadowedB := by
  rintro ⟨n, hf, r, hr, -⟩
  have hfind : find shadowedWord shadowedA = some shadowedFirst := by decide
  rw [hfind] at hf
  injection hf with hn
  subst hn
  cases hr

/-! ## The admission index -/

/-- The admission index of an address: the position of the binding
`find` answers with, and `w.length` when the word binds the address
nowhere. It mirrors `find`'s recursion step for step, which is what
makes it the index of the occurrence the edge was read from. -/
def firstIndex : Word → Addr32 → Nat
  | [], _ => 0
  | ⟨c, _⟩ :: rest, b => if b = c then 0 else firstIndex rest b + 1

/-- A bound address is indexed inside the word. -/
theorem firstIndex_lt_length {w : Word} {b : Addr32} (h : (find w b).isSome) :
    firstIndex w b < w.length := by
  induction w with
  | nil => simp [find] at h
  | cons e rest ih =>
    obtain ⟨c, m⟩ := e
    by_cases hb : b = c
    · simp [firstIndex, hb]
    · have h' : (find rest b).isSome := by simpa [find, hb] using h
      simp only [firstIndex, if_neg hb, List.length_cons]
      exact Nat.succ_lt_succ (ih h')

/-- Growth does not move a bound address's index. The first binding is
where it always was; only unbound addresses move, and they move because
`w.length` moved. -/
theorem firstIndex_append_of_isSome {w : Word} {b : Addr32}
    (h : (find w b).isSome) (v : Word) :
    firstIndex (w ++ v) b = firstIndex w b := by
  induction w with
  | nil => simp [find] at h
  | cons e rest ih =>
    obtain ⟨c, m⟩ := e
    by_cases hb : b = c
    · simp [firstIndex, hb]
    · have h' : (find rest b).isSome := by simpa [find, hb] using h
      simp only [List.cons_append, firstIndex, if_neg hb]
      rw [ih h']

/-- An address resolving inside a PREFIX is indexed inside that prefix.
This is the step that converts "resolves strictly earlier" into a
number. -/
theorem firstIndex_lt_of_take {w : Word} {b : Addr32} {k : Nat}
    (h : (find (w.take k) b).isSome) : firstIndex w b < k := by
  have h1 : firstIndex (w.take k) b < (w.take k).length := firstIndex_lt_length h
  have h2 : (w.take k).length ≤ k := List.length_take_le k w
  have h3 : firstIndex (w.take k ++ w.drop k) b = firstIndex (w.take k) b :=
    firstIndex_append_of_isSome h _
  rw [List.take_append_drop] at h3
  omega

/-! ## Admission, read as a prefix statement

`wfFrom_resolves` (Word.lean) says an admitted word resolves its
references in the WHOLE word — enough for `Store.Closed`. Reachability
needs the sharper reading the scan actually performs: each binding's
references resolve in the prefix strictly before it. -/

/-- The scan's own statement, with the already-admitted prefix
explicit: the node `find` answers with at `a` had every reference
resolving in `prior` plus the part of the word strictly before that
binding. -/
theorem wfFrom_refs_prefix : ∀ (w prior : Word), wfFrom prior w = true →
    ∀ {a : Addr32} {n : Node}, find w a = some n →
    ∀ {r : Ref}, r ∈ n.refs →
    resolvesIn (prior ++ w.take (firstIndex w a)) r = true := by
  intro w
  induction w with
  | nil => intro prior _ a n hf; simp [find] at hf
  | cons e rest ih =>
    obtain ⟨c, m⟩ := e
    intro prior h a n hf r hr
    simp only [wfFrom, Bool.and_eq_true] at h
    obtain ⟨hrefs, hrest⟩ := h
    by_cases hac : a = c
    · have hn : n = m := by
        simp only [find, if_pos hac] at hf
        exact (Option.some.inj hf).symm
      have hidx : firstIndex (Binding.mk c m :: rest) a = 0 := by
        simp [firstIndex, hac]
      rw [hidx]
      simp only [List.take_zero, List.append_nil]
      exact List.all_eq_true.mp hrefs r (hn ▸ hr)
    · have hf' : find rest a = some n := by simpa [find, hac] using hf
      have hidx : firstIndex (Binding.mk c m :: rest) a = firstIndex rest a + 1 := by
        simp [firstIndex, hac]
      rw [hidx]
      have hlift := ih (prior ++ [Binding.mk c m]) hrest hf' hr
      simpa using hlift

/-- Admission, as the prefix statement reachability needs: the resident
node at `a` had every reference resolving strictly before `a`'s own
binding. -/
theorem wf_refs_prefix {w : Word} (hw : wf w = true) {a : Addr32} {n : Node}
    (hf : find w a = some n) {r : Ref} (hr : r ∈ n.refs) :
    resolvesIn (w.take (firstIndex w a)) r = true := by
  have h := wfFrom_refs_prefix w [] hw hf hr
  simpa using h

/-- **ADMISSION ORDER IS A TOPOLOGICAL SORT OF THE REFERENCE GRAPH.**
Every edge moves strictly one way along the admission index: the target
of a reference was bound strictly before the node that references it.
The direction is `wfFrom`'s, not a convention — the scan hands each
binding the prefix before it and nothing else, so an edge cannot point
forward or sideways. -/
theorem wf_edge_index {w : Word} (hw : wf w = true) {a b : Addr32}
    (h : Edge w a b) : firstIndex w b < firstIndex w a := by
  obtain ⟨n, hf, r, hr, hrb⟩ := h
  have hres := wf_refs_prefix hw hf hr
  obtain ⟨m, hm, _⟩ := resolvesIn_iff.mp hres
  have hsome : (find (w.take (firstIndex w a)) b).isSome := by
    rw [← hrb, hm]; rfl
  exact firstIndex_lt_of_take hsome

/-! ## The closure -/

/-- REACHABILITY: the reflexive-transitive closure of the reference
edge, minted in-tree with `Relation.ReflTransGen`'s exact shape — a
reflexive base and a `tail` step that extends a path by one edge at its
far end. "Everything about X" is `Reach w x`. -/
inductive Reach (w : Word) (a : Addr32) : Addr32 → Prop where
  | refl : Reach w a a
  | tail {b c : Addr32} : Reach w a b → Edge w b c → Reach w a c

/-- One edge is a path. -/
theorem Reach.single {w : Word} {a b : Addr32} (h : Edge w a b) : Reach w a b :=
  Reach.tail Reach.refl h

/-- Paths compose. -/
theorem Reach.trans {w : Word} {a b c : Addr32} (hab : Reach w a b)
    (hbc : Reach w b c) : Reach w a c := by
  induction hbc with
  | refl => exact hab
  | tail _ he ih => exact Reach.tail ih he

/-- A path extended at its NEAR end. `tail` grows a path forward; a
search grows it backward, so both directions are wanted. -/
theorem Reach.head {w : Word} {a b c : Addr32} (hab : Edge w a b)
    (hbc : Reach w b c) : Reach w a c :=
  Reach.trans (Reach.single hab) hbc

/-- The path read from its FIRST step. `Reach` is built at the far end,
so this is the inversion a forward search needs: a path is empty, or it
takes one edge and then is a path again. -/
theorem Reach.cases_head {w : Word} {a b : Addr32} (h : Reach w a b) :
    a = b ∨ ∃ c, Edge w a c ∧ Reach w c b := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail b' c hab' hb'c ih =>
    rcases ih with heq | ⟨d, had, hdb'⟩
    · subst heq; exact Or.inr ⟨c, hb'c, Reach.refl⟩
    · exact Or.inr ⟨d, had, Reach.tail hdb' hb'c⟩

/-- **THE PATCHABILITY LICENCE.** Reachability persists under append:
what was reachable stays reachable as the word grows. The answer to
"everything about X" is therefore patched by growth rather than
recomputed at a cut, and no admission premise is needed — grow-only is
the whole argument. -/
theorem reach_mono {w : Word} (v : Word) {a b : Addr32} (h : Reach w a b) :
    Reach (w ++ v) a b := by
  induction h with
  | refl => exact Reach.refl
  | tail _ he ih => exact Reach.tail ih (edge_mono v he)

/-- A path is either empty or strictly descends the admission index —
the topological statement lifted from one edge to the whole walk. -/
theorem reach_index {w : Word} (hw : wf w = true) {a b : Addr32}
    (h : Reach w a b) : a = b ∨ firstIndex w b < firstIndex w a := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ he ih =>
    rcases ih with heq | hlt
    · subst heq
      exact Or.inr (wf_edge_index hw he)
    · exact Or.inr (Nat.lt_trans (wf_edge_index hw he) hlt)

/-- **ACYCLICITY.** In an admitted word, two addresses that reach each
other are the same address. The resident reference graph is a DAG, and
it is one because the admission scan already refused anything else —
nothing beyond `wf` is assumed, and no ordering has to be constructed.
-/
theorem reach_acyclic {w : Word} (hw : wf w = true) {a b : Addr32}
    (hab : Reach w a b) (hba : Reach w b a) : a = b := by
  rcases reach_index hw hab with h1 | h1
  · exact h1
  · rcases reach_index hw hba with h2 | h2
    · exact h2.symm
    · omega

/-! ## The closure, decided

Mathlib defines `ReflTransGen` and decides nothing about it. Here the
closure IS decided, and the reason is the theorem above: every edge
strictly descends the admission index, so a path out of `a` is shorter
than `firstIndex w a`, and a bounded search at that depth is complete
rather than merely sound. The termination measure is a consequence of
admission, not a fuel parameter someone picked. -/

/-- The successors of an address: what the RESIDENT node at `a`
references, in the order the node lists them. Unbound addresses have
none. -/
def succs (w : Word) (a : Addr32) : List Addr32 :=
  match find w a with
  | some n => n.refs.map (·.addr)
  | none => []

/-- The successor list is the edge relation, enumerated. -/
theorem mem_succs_iff {w : Word} {a c : Addr32} : c ∈ succs w a ↔ Edge w a c := by
  unfold succs Edge
  cases hf : find w a with
  | none => simp
  | some n => simp

/-- Bounded reachability, as a computation: `reachIn w b k a` is `true`
exactly when `a` reaches `b` along at most `k` edges. The word and the
TARGET are fixed and the SOURCE moves, because the search walks
forward, which is why the source sits last.

The address test is spelled `decide (a = b)` rather than `a == b`, and
that is not cosmetic: `Addr32` is a subtype, and `Subtype.instReflBEq`
— the instance `beq_self_eq_true` resolves through — depends on
`Classical.choice`, which would put this module outside the estate's
axiom ceiling for no gain. `find` already tests addresses this way.
Measured, not assumed: `lake exe axioms` reports every declaration in
this module at `propext`/`Quot.sound` or below. -/
def reachIn (w : Word) (b : Addr32) : Nat → Addr32 → Bool
  | 0, a => decide (a = b)
  | k + 1, a => decide (a = b) || (succs w a).any (fun c => reachIn w b k c)

/-- The search finds its own target at any depth. -/
theorem reachIn_self (w : Word) (b : Addr32) (k : Nat) : reachIn w b k b = true := by
  cases k with
  | zero => exact decide_eq_true rfl
  | succ k =>
    show (decide (b = b) || (succs w b).any (fun c => reachIn w b k c)) = true
    rw [decide_eq_true rfl, Bool.true_or]

/-- Soundness of the bounded search, and it needs no premise: a search
that says yes exhibits a path. -/
theorem reachIn_sound {w : Word} {b : Addr32} :
    ∀ (k : Nat) (a : Addr32), reachIn w b k a = true → Reach w a b := by
  intro k
  induction k with
  | zero =>
    intro a h
    have hab : a = b := of_decide_eq_true h
    subst hab; exact Reach.refl
  | succ k ih =>
    intro a h
    simp only [reachIn, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq] at h
    rcases h with hab | ⟨c, hc, hrec⟩
    · subst hab; exact Reach.refl
    · exact Reach.head (mem_succs_iff.mp hc) (ih c hrec)

/-- Completeness of the bounded search, at the depth admission
supplies: in an admitted word, any path out of `a` is found within
`firstIndex w a` steps. This is where `wf` is consumed — the strict
descent of `wf_edge_index` is what stops a path from outrunning the
bound. -/
theorem reachIn_complete {w : Word} (hw : wf w = true) {b : Addr32} :
    ∀ (k : Nat) {a : Addr32}, Reach w a b → firstIndex w a ≤ k →
      reachIn w b k a = true := by
  intro k
  induction k with
  | zero =>
    intro a h hle
    rcases Reach.cases_head h with heq | ⟨c, hac, _⟩
    · subst heq; exact reachIn_self _ _ _
    · have hlt := wf_edge_index hw hac
      omega
  | succ k ih =>
    intro a h hle
    rcases Reach.cases_head h with heq | ⟨c, hac, hcb⟩
    · subst heq; exact reachIn_self _ _ _
    · have hlt := wf_edge_index hw hac
      have hrec : reachIn w b k c = true := ih hcb (by omega)
      simp only [reachIn, Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨c, mem_succs_iff.mpr hac, hrec⟩

/-- An address's index never exceeds the word's length — the bound the
search is run at. -/
theorem firstIndex_le_length (w : Word) (b : Addr32) :
    firstIndex w b ≤ w.length := by
  induction w with
  | nil => simp [firstIndex]
  | cons e rest ih =>
    obtain ⟨c, m⟩ := e
    by_cases hb : b = c
    · simp [firstIndex, hb]
    · simp only [firstIndex, if_neg hb, List.length_cons]
      omega

/-- REACHABILITY, DECIDED: the search run at the word's own length. -/
def reachB (w : Word) (a b : Addr32) : Bool := reachIn w b w.length a

/-- The decision never lies: `true` exhibits a path, on any word. -/
theorem reachB_sound {w : Word} {a b : Addr32} (h : reachB w a b = true) :
    Reach w a b := reachIn_sound _ _ h

/-- The decision misses nothing, on an ADMITTED word. -/
theorem reachB_complete {w : Word} (hw : wf w = true) {a b : Addr32}
    (h : Reach w a b) : reachB w a b = true :=
  reachIn_complete hw _ h (firstIndex_le_length w a)

/-- The two halves together: over an admitted word the computation and
the relation are the same question. -/
theorem reachB_iff {w : Word} (hw : wf w = true) {a b : Addr32} :
    reachB w a b = true ↔ Reach w a b :=
  ⟨reachB_sound, reachB_complete hw⟩

/-- The decision procedure. It carries NO `instance` attribute, on
purpose: its premise is `wf w`, which instance resolution cannot
supply, and the honest reading is that admission is what makes
reachability decidable here. Soundness alone holds without it
(`reachB_sound`). -/
def decidableReach {w : Word} (hw : wf w = true) (a b : Addr32) :
    Decidable (Reach w a b) :=
  decidable_of_iff (reachB w a b = true) (reachB_iff hw)

end Word

end Cas
