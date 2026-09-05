import Effect4.Char.Conformance.VectorSet

/-!
# Conformance.Generators: the four monotone generators

Owner: every way a `VectorSet` is populated. Four generators, each a total
function and each `GSet.ofList` of a list that only grows with its inputs, so
monotonicity is `GSet.ofList_mono` once and soundness is `factOf_idem` once.

| Generator | Input | Tag |
| --- | --- | --- |
| `fromSuite` | the authored `Suite` | `authored test` |
| `fromMutants` | the suite and the declared `Mutant`s | `mutantKill` / `mutantSurvives` |
| `enumerate`, `enumerateRefused` | a finite alphabet and a depth | `enumerated depth` / `refused depth` |
| `fromDoctests` | ratified `Doctest`s | `doctest span ratifiedBy` |

Where it sits in the semantic compiler: the **front-end lowering**. The LLM
writes the five parts (carriers, step, invariants, tests, mutants); these
functions lower them to the intermediate representation. What each makes
mechanical: `enumerate` is the one that needs no thought at all, and its
completeness theorem `mem_wordsUpTo_of_accepts` is the guarantee that up to the
depth nothing is missed; `fromMutants` turns "does the suite separate the
mutant" into a tag the set carries; `fromDoctests` takes the one human step, the
ratification, as data and reports a disagreement as a finding row
(`doctestFindings`), never as a changed vector.

## The algebra of the enumeration

| | |
| --- | --- |
| Carrier | `wordsUpTo M alpha k : List (List L)`, the accepted words over `alpha` of length at most `k` |
| Operations | `successors`, `frontier`, `wordsUpTo`, `refusalsOf` |
| Laws | `accepts_of_mem_wordsUpTo` (sound), `mem_wordsUpTo_of_accepts` (complete), `length_of_mem_frontier`, `mem_wordsUpTo_mono` (depth), `mem_wordsUpTo_mono_alpha` (alphabet) |
| Structure | the frontier of the reachability least fixed point, restricted to the submonoid `alpha` generates and cut at depth `k`; the set of accepted words is prefix-closed (`Machine.accepts_prefix`), which is what makes the frontier recursion complete |
| Payoff | deletes the hand-chosen test list as the only vector source; a coding LLM adds depth or a verb, never a word |
| Anti-vacuity | `Conformance/Cell.lean`: `enumeration_alone_spares_lossy` beside `refusals_kill_lossy`, so the accepted enumeration and the refusals are shown to be different sets with different power |
| Generation | mechanical |

The budget: `wordsUpTo` grows with the branching of the machine, not with the
alphabet's size alone; the measurement is in
`docs/research/2026-09-05-workshop-char/10-conformance/03-generators.md`.
-/

set_option autoImplicit false

namespace Effect4.Char

/-! ## The enumeration, over the machine alone -/

section Enumeration

variable {S L : Type}

/-- One-step extensions of a word by every enabled label of the alphabet. -/
def successors (M : Machine S L) (alpha : List L) (w : List L) : List (List L) :=
  match M.run M.init w with
  | some s => alpha.filterMap fun l => if M.enabled s l then some (w ++ [l]) else none
  | none => []

theorem successors_some (M : Machine S L) (alpha : List L) {w : List L} {s : S}
    (h : M.run M.init w = some s) :
    successors M alpha w = alpha.filterMap fun l => if M.enabled s l then some (w ++ [l]) else none := by
  simp [successors, h]

theorem successors_none (M : Machine S L) (alpha : List L) {w : List L}
    (h : M.run M.init w = none) : successors M alpha w = [] := by
  simp [successors, h]

/-- The accepted words of exactly length `k` over the alphabet. -/
def frontier (M : Machine S L) (alpha : List L) : Nat → List (List L)
  | 0 => [[]]
  | k + 1 => (frontier M alpha k).flatMap (successors M alpha)

/-- The accepted words of length at most `k` over the alphabet. -/
def wordsUpTo (M : Machine S L) (alpha : List L) : Nat → List (List L)
  | 0 => [[]]
  | k + 1 => wordsUpTo M alpha k ++ frontier M alpha (k + 1)

theorem wordsUpTo_succ (M : Machine S L) (alpha : List L) (k : Nat) :
    wordsUpTo M alpha (k + 1) = wordsUpTo M alpha k ++ frontier M alpha (k + 1) := rfl

/-- Depth monotonicity. -/
theorem mem_wordsUpTo_mono (M : Machine S L) (alpha : List L) {k : Nat} {w : List L}
    (h : w ∈ wordsUpTo M alpha k) : ∀ n, w ∈ wordsUpTo M alpha (k + n)
  | 0 => h
  | n + 1 => by
    rw [show k + (n + 1) = (k + n) + 1 from rfl, wordsUpTo_succ]
    exact List.mem_append.2 (Or.inl (mem_wordsUpTo_mono M alpha h n))

theorem mem_frontier_of_mem_wordsUpTo (M : Machine S L) (alpha : List L) :
    ∀ (k : Nat) {w : List L}, w ∈ wordsUpTo M alpha k → ∃ j, j ≤ k ∧ w ∈ frontier M alpha j
  | 0, w, h => ⟨0, Nat.le_refl 0, h⟩
  | k + 1, w, h => by
    rw [wordsUpTo_succ] at h
    rcases List.mem_append.1 h with h | h
    · obtain ⟨j, hj, hw⟩ := mem_frontier_of_mem_wordsUpTo M alpha k h
      exact ⟨j, Nat.le_succ_of_le hj, hw⟩
    · exact ⟨k + 1, Nat.le_refl _, h⟩

/-- A word on the frontier is one enabled step past a word of the frontier below. -/
theorem mem_frontier_succ (M : Machine S L) (alpha : List L) (k : Nat) {w : List L}
    (h : w ∈ frontier M alpha (k + 1)) :
    ∃ u s l, u ∈ frontier M alpha k ∧ M.run M.init u = some s ∧ l ∈ alpha ∧
      M.enabled s l = true ∧ w = u ++ [l] := by
  simp only [frontier] at h
  obtain ⟨u, hu, hw⟩ := List.mem_flatMap.1 h
  cases hrun : M.run M.init u with
  | none => rw [successors_none M alpha hrun] at hw; exact absurd hw (by simp)
  | some s =>
    rw [successors_some M alpha hrun] at hw
    obtain ⟨l, hl, hl'⟩ := List.mem_filterMap.1 hw
    by_cases he : M.enabled s l = true
    · rw [if_pos he] at hl'
      exact ⟨u, s, l, hu, hrun, hl, he, (Option.some.inj hl').symm⟩
    · rw [if_neg he] at hl'; exact absurd hl' (by simp)

/-- An enabled step past an accepted word is accepted. -/
theorem accepts_append_single (M : Machine S L) {u : List L} {s : S} {l : L}
    (hrun : M.run M.init u = some s) (he : M.enabled s l = true) :
    M.accepts (u ++ [l]) = true := by
  unfold Machine.accepts
  rw [Machine.run_append, hrun]
  unfold Machine.enabled at he
  cases hst : M.step s l with
  | none => rw [hst] at he; simp at he
  | some s' => simp [Machine.run, hst]

/-- Every word on the frontier is accepted by the model. -/
theorem accepts_of_mem_frontier (M : Machine S L) (alpha : List L) :
    ∀ (k : Nat) {w : List L}, w ∈ frontier M alpha k → M.accepts w = true
  | 0, w, h => by
    simp only [frontier, List.mem_singleton] at h
    subst h; rfl
  | k + 1, w, h => by
    obtain ⟨u, s, l, _, hrun, _, he, rfl⟩ := mem_frontier_succ M alpha k h
    exact accepts_append_single M hrun he

theorem accepts_of_mem_wordsUpTo (M : Machine S L) (alpha : List L) {k : Nat} {w : List L}
    (h : w ∈ wordsUpTo M alpha k) : M.accepts w = true := by
  obtain ⟨j, _, hw⟩ := mem_frontier_of_mem_wordsUpTo M alpha k h
  exact accepts_of_mem_frontier M alpha j hw

/-- Every word on the frontier has the frontier's length. -/
theorem length_of_mem_frontier (M : Machine S L) (alpha : List L) :
    ∀ (k : Nat) {w : List L}, w ∈ frontier M alpha k → w.length = k
  | 0, w, h => by
    simp only [frontier, List.mem_singleton] at h
    subst h; rfl
  | k + 1, w, h => by
    obtain ⟨u, _, _, hu, _, _, _, rfl⟩ := mem_frontier_succ M alpha k h
    rw [List.length_append, length_of_mem_frontier M alpha k hu]; rfl

/-- **Completeness of the enumeration.** Every accepted word over the alphabet of
length `k` is on the frontier at `k`. Up to the depth, nothing is missed. -/
theorem mem_frontier_of_accepts (M : Machine S L) (alpha : List L) :
    ∀ (k : Nat) (w : List L), w.length = k → M.accepts w = true →
      (∀ l ∈ w, l ∈ alpha) → w ∈ frontier M alpha k
  | 0, w, hlen, _, _ => by
    cases w with
    | nil => exact List.mem_singleton.2 rfl
    | cons _ _ => exact absurd hlen (Nat.succ_ne_zero _)
  | k + 1, w, hlen, hacc, halpha => by
    rcases List.eq_nil_or_concat w with rfl | ⟨u, l, rfl⟩
    · exact absurd hlen.symm (Nat.succ_ne_zero k)
    · rw [List.concat_eq_append] at hlen hacc halpha ⊢
      have hlenu : u.length = k := by
        rw [List.length_append] at hlen; exact Nat.succ.inj hlen
      have haccu : M.accepts u = true := M.accepts_prefix u [l] hacc
      have hu : u ∈ frontier M alpha k :=
        mem_frontier_of_accepts M alpha k u hlenu haccu
          (fun x hx => halpha x (List.mem_append.2 (Or.inl hx)))
      simp only [frontier]
      refine List.mem_flatMap.2 ⟨u, hu, ?_⟩
      unfold Machine.accepts at hacc
      rw [Machine.run_append] at hacc
      cases hrun : M.run M.init u with
      | none => rw [hrun] at hacc; exact Bool.noConfusion hacc
      | some s =>
        rw [hrun] at hacc
        rw [successors_some M alpha hrun]
        refine List.mem_filterMap.2
          ⟨l, halpha l (List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl))), ?_⟩
        have he : M.enabled s l = true := by
          unfold Machine.enabled
          cases hst : M.step s l with
          | none =>
            change (M.run s [l]).isSome = true at hacc
            rw [Machine.run_cons, hst] at hacc; exact Bool.noConfusion hacc
          | some _ => rfl
        rw [if_pos he]

theorem mem_wordsUpTo_of_accepts (M : Machine S L) (alpha : List L) (k : Nat) (w : List L)
    (hlen : w.length ≤ k) (hacc : M.accepts w = true) (halpha : ∀ l ∈ w, l ∈ alpha) :
    w ∈ wordsUpTo M alpha k := by
  obtain ⟨n, hn⟩ := Nat.le.dest hlen
  have hw : w ∈ wordsUpTo M alpha w.length := by
    cases hl : w.length with
    | zero => rw [List.length_eq_zero_iff] at hl; subst hl; exact List.mem_singleton.2 rfl
    | succ j =>
      rw [wordsUpTo_succ]
      exact List.mem_append.2 (Or.inr (mem_frontier_of_accepts M alpha (j + 1) w hl hacc halpha))
  rw [← hn]; exact mem_wordsUpTo_mono M alpha hw n

/-- Alphabet monotonicity of the frontier: adding a verb keeps every word. -/
theorem mem_frontier_mono_alpha (M : Machine S L) {alpha alpha' : List L}
    (hsub : ∀ l ∈ alpha, l ∈ alpha') :
    ∀ (k : Nat) {w : List L}, w ∈ frontier M alpha k → w ∈ frontier M alpha' k
  | 0, _, h => h
  | k + 1, w, h => by
    obtain ⟨u, s, l, hu, hrun, hl, he, rfl⟩ := mem_frontier_succ M alpha k h
    simp only [frontier]
    refine List.mem_flatMap.2 ⟨u, mem_frontier_mono_alpha M hsub k hu, ?_⟩
    rw [successors_some M alpha' hrun]
    exact List.mem_filterMap.2 ⟨l, hsub l hl, by rw [if_pos he]⟩

theorem mem_wordsUpTo_mono_alpha (M : Machine S L) {alpha alpha' : List L}
    (hsub : ∀ l ∈ alpha, l ∈ alpha') :
    ∀ (k : Nat) {w : List L}, w ∈ wordsUpTo M alpha k → w ∈ wordsUpTo M alpha' k
  | 0, _, h => h
  | k + 1, w, h => by
    rw [wordsUpTo_succ] at h ⊢
    rcases List.mem_append.1 h with h | h
    · exact List.mem_append.2 (Or.inl (mem_wordsUpTo_mono_alpha M hsub k h))
    · exact List.mem_append.2 (Or.inr (mem_frontier_mono_alpha M hsub (k + 1) h))

/-- One-step refusals of an accepted word: the labels of the alphabet the reached
state disables. -/
def refusalsOf (M : Machine S L) (alpha : List L) (w : List L) : List (List L) :=
  match M.run M.init w with
  | some s => alpha.filterMap fun l => if M.enabled s l then none else some (w ++ [l])
  | none => []

theorem refusalsOf_some (M : Machine S L) (alpha : List L) {w : List L} {s : S}
    (h : M.run M.init w = some s) :
    refusalsOf M alpha w =
      alpha.filterMap fun l => if M.enabled s l then none else some (w ++ [l]) := by
  simp [refusalsOf, h]

theorem refusalsOf_none (M : Machine S L) (alpha : List L) {w : List L}
    (h : M.run M.init w = none) : refusalsOf M alpha w = [] := by
  simp [refusalsOf, h]

/-- Every refusal is a refused word. -/
theorem refuses_of_mem_refusalsOf (M : Machine S L) (alpha : List L) {u w : List L}
    (h : w ∈ refusalsOf M alpha u) : M.accepts w = false := by
  cases hrun : M.run M.init u with
  | none => rw [refusalsOf_none M alpha hrun] at h; exact absurd h (by simp)
  | some s =>
    rw [refusalsOf_some M alpha hrun] at h
    obtain ⟨l, _, hl⟩ := List.mem_filterMap.1 h
    by_cases he : M.enabled s l = true
    · rw [if_pos he] at hl; exact absurd hl (by simp)
    · rw [if_neg he] at hl
      cases hl
      unfold Machine.accepts
      rw [Machine.run_append, hrun]
      unfold Machine.enabled at he
      cases hst : M.step s l with
      | none => simp [Machine.run, hst]
      | some _ => rw [hst] at he; exact absurd rfl he

end Enumeration

/-! ## The generators, into the vector set -/

section Generators

variable {S L C : Type} [DecidableEq L] [DecidableEq C]

/-- Authored tests become vectors. The vector is the model's fact for the test's
word, not the test's own expectation; whether the two agree is the suite's own
receipt (`Suite.run`), a separate `Bool`. -/
def fromSuite (M : Machine S L) (R : Reading S L C) (clients : List C) (ts : Suite L C) :
    VectorSet L C :=
  GSet.ofList (ts.map fun t => (factOf M R clients t.labels, .authored t.name))

theorem fromSuite_sound (M : Machine S L) (R : Reading S L C) (clients : List C)
    (ts : Suite L C) : VectorSet.Sound M R clients (fromSuite M R clients ts) :=
  VectorSet.sound_ofList fun x hx => by
    obtain ⟨t, _, rfl⟩ := List.mem_map.1 hx
    exact factOf_idem M R clients t.labels

theorem fromSuite_mono (M : Machine S L) (R : Reading S L C) (clients : List C)
    (ts more : Suite L C) :
    GSet.Sub (fromSuite M R clients ts) (fromSuite M R clients (ts ++ more)) :=
  GSet.ofList_mono fun x hx => by
    rw [List.map_append]; exact List.mem_append.2 (Or.inl hx)

/-- Which tag a mutant earns on a test's word: separated by the model's fact or not. -/
def mutantTag (M : Machine S L) (R : Reading S L C) (clients : List C) (m : Mutant S L)
    (t : Test L C) : Provenance :=
  if factOf m.machine R clients t.labels = factOf M R clients t.labels
  then .mutantSurvives m.id t.name else .mutantKill m.id t.name

/-- For each mutant and each test, the model's vector for the test's word, tagged
with whether that word separates the mutant. Both tags are labels; the kill
receipt is `VectorSet.kills`, decided over the set. -/
def fromMutants (M : Machine S L) (R : Reading S L C) (clients : List C) (ts : Suite L C)
    (ms : List (Mutant S L)) : VectorSet L C :=
  GSet.ofList (ms.flatMap fun m => ts.map fun t =>
    (factOf M R clients t.labels, mutantTag M R clients m t))

theorem fromMutants_sound (M : Machine S L) (R : Reading S L C) (clients : List C)
    (ts : Suite L C) (ms : List (Mutant S L)) :
    VectorSet.Sound M R clients (fromMutants M R clients ts ms) :=
  VectorSet.sound_ofList fun x hx => by
    obtain ⟨m, _, hx⟩ := List.mem_flatMap.1 hx
    obtain ⟨t, _, rfl⟩ := List.mem_map.1 hx
    exact factOf_idem M R clients t.labels

theorem fromMutants_mono_mutants (M : Machine S L) (R : Reading S L C) (clients : List C)
    (ts : Suite L C) (ms more : List (Mutant S L)) :
    GSet.Sub (fromMutants M R clients ts ms) (fromMutants M R clients ts (ms ++ more)) :=
  GSet.ofList_mono fun x hx => by
    rw [List.flatMap_append]; exact List.mem_append.2 (Or.inl hx)

theorem fromMutants_mono_tests (M : Machine S L) (R : Reading S L C) (clients : List C)
    (ts more : Suite L C) (ms : List (Mutant S L)) :
    GSet.Sub (fromMutants M R clients ts ms) (fromMutants M R clients (ts ++ more) ms) :=
  GSet.ofList_mono fun x hx => by
    obtain ⟨m, hm, hx⟩ := List.mem_flatMap.1 hx
    exact List.mem_flatMap.2 ⟨m, hm, by rw [List.map_append]; exact List.mem_append.2 (Or.inl hx)⟩

/-- **Bounded enumeration.** Every accepted word over the alphabet up to depth
`k`, as the model's vectors, tagged by depth. Complete (`mem_wordsUpTo_of_accepts`),
sound (`enumerate_sound`), monotone in the depth and in the alphabet. -/
def enumerate (M : Machine S L) (R : Reading S L C) (clients : List C) (alpha : List L)
    (k : Nat) : VectorSet L C :=
  GSet.ofList ((wordsUpTo M alpha k).map fun w => (factOf M R clients w, .enumerated w.length))

theorem enumerate_sound (M : Machine S L) (R : Reading S L C) (clients : List C)
    (alpha : List L) (k : Nat) : VectorSet.Sound M R clients (enumerate M R clients alpha k) :=
  VectorSet.sound_ofList fun x hx => by
    obtain ⟨w, _, rfl⟩ := List.mem_map.1 hx
    exact factOf_idem M R clients w

theorem enumerate_mono_depth (M : Machine S L) (R : Reading S L C) (clients : List C)
    (alpha : List L) (k n : Nat) :
    GSet.Sub (enumerate M R clients alpha k) (enumerate M R clients alpha (k + n)) :=
  GSet.ofList_mono fun x hx => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
    exact List.mem_map.2 ⟨w, mem_wordsUpTo_mono M alpha hw n, rfl⟩

theorem enumerate_mono_alpha (M : Machine S L) (R : Reading S L C) (clients : List C)
    {alpha alpha' : List L} (hsub : ∀ l ∈ alpha, l ∈ alpha') (k : Nat) :
    GSet.Sub (enumerate M R clients alpha k) (enumerate M R clients alpha' k) :=
  GSet.ofList_mono fun x hx => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
    exact List.mem_map.2 ⟨w, mem_wordsUpTo_mono_alpha M hsub k hw, rfl⟩

/-- Every enumerated fact is an accepted word. -/
theorem enumerate_accept (M : Machine S L) (R : Reading S L C) (clients : List C)
    (alpha : List L) (k : Nat) {f : Fact L C} {p : Provenance}
    (h : (enumerate M R clients alpha k).has (f, p) = true) : f.accept = true := by
  obtain ⟨w, hw, hx⟩ := List.mem_map.1 (GSet.mem_ofList.1 h)
  have : f = factOf M R clients w := (Prod.mk.inj hx).1.symm
  rw [this, factOf_accept]
  exact accepts_of_mem_wordsUpTo M alpha hw

/-- **Bounded refusals.** For every enumerated word, each one-step extension the
model refuses, as a negative vector. These are what kill a mutant that accepts
too much; whether a refusal is replayable on the host is a per-verb decision the
fixture records, not one decided here. -/
def enumerateRefused (M : Machine S L) (R : Reading S L C) (clients : List C) (alpha : List L)
    (k : Nat) : VectorSet L C :=
  GSet.ofList (((wordsUpTo M alpha k).flatMap (refusalsOf M alpha)).map fun w =>
    (factOf M R clients w, .refused w.length))

theorem enumerateRefused_sound (M : Machine S L) (R : Reading S L C) (clients : List C)
    (alpha : List L) (k : Nat) :
    VectorSet.Sound M R clients (enumerateRefused M R clients alpha k) :=
  VectorSet.sound_ofList fun x hx => by
    obtain ⟨w, _, rfl⟩ := List.mem_map.1 hx
    exact factOf_idem M R clients w

theorem enumerateRefused_mono_depth (M : Machine S L) (R : Reading S L C) (clients : List C)
    (alpha : List L) (k n : Nat) :
    GSet.Sub (enumerateRefused M R clients alpha k) (enumerateRefused M R clients alpha (k + n)) :=
  GSet.ofList_mono fun x hx => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
    obtain ⟨u, hu, hw⟩ := List.mem_flatMap.1 hw
    exact List.mem_map.2 ⟨w, List.mem_flatMap.2 ⟨u, mem_wordsUpTo_mono M alpha hu n, hw⟩, rfl⟩

/-- Every refused fact is a refused word. -/
theorem enumerateRefused_refuses (M : Machine S L) (R : Reading S L C) (clients : List C)
    (alpha : List L) (k : Nat) {f : Fact L C} {p : Provenance}
    (h : (enumerateRefused M R clients alpha k).has (f, p) = true) : f.accept = false := by
  obtain ⟨w, hw, hx⟩ := List.mem_map.1 (GSet.mem_ofList.1 h)
  have hf : f = factOf M R clients w := (Prod.mk.inj hx).1.symm
  obtain ⟨u, _, hw⟩ := List.mem_flatMap.1 hw
  rw [hf, factOf_accept]
  exact refuses_of_mem_refusalsOf M alpha hw

/-- A pinned doctest, translated into a word over the alphabet, with the
expectation a human ratified. The translation and the ratification are the two
hand steps of the doctest lane; both are data here. -/
structure Doctest (L C : Type) where
  /-- The span digest of the doctest block in the pinned file, as hex. -/
  span : String
  word : List L
  expectAccept : Bool
  expectReadings : List (ClientReading C)
  ratifiedBy : String
deriving DecidableEq, Repr

/-- Does the model agree with the ratified expectation. A disagreement is a
finding row, never a change to the vector. -/
def Doctest.agrees (M : Machine S L) (R : Reading S L C) (clients : List C)
    (d : Doctest L C) : Bool :=
  decide (factOf M R clients d.word = ⟨d.word, d.expectAccept, d.expectReadings⟩)

/-- Ratified doctests become vectors: the **model's** fact for the doctest's word,
tagged with the span and the ratifier. -/
def fromDoctests (M : Machine S L) (R : Reading S L C) (clients : List C)
    (ds : List (Doctest L C)) : VectorSet L C :=
  GSet.ofList (ds.map fun d => (factOf M R clients d.word, .doctest d.span d.ratifiedBy))

/-- The spans whose ratified expectation the model does not reproduce. -/
def doctestFindings (M : Machine S L) (R : Reading S L C) (clients : List C)
    (ds : List (Doctest L C)) : List String :=
  (ds.filter fun d => !d.agrees M R clients).map Doctest.span

theorem fromDoctests_sound (M : Machine S L) (R : Reading S L C) (clients : List C)
    (ds : List (Doctest L C)) : VectorSet.Sound M R clients (fromDoctests M R clients ds) :=
  VectorSet.sound_ofList fun x hx => by
    obtain ⟨d, _, rfl⟩ := List.mem_map.1 hx
    exact factOf_idem M R clients d.word

theorem fromDoctests_mono (M : Machine S L) (R : Reading S L C) (clients : List C)
    (ds more : List (Doctest L C)) :
    GSet.Sub (fromDoctests M R clients ds) (fromDoctests M R clients (ds ++ more)) :=
  GSet.ofList_mono fun x hx => by
    rw [List.map_append]; exact List.mem_append.2 (Or.inl hx)

end Generators

end Effect4.Char
