import Effects.Merkle.Decoder

/-!
# The MRK-1 laws

Run composition (the fragmentation carrier), the per-step emission and
length gates, run-level emission soundness with the collision-witness
disjunct (stated so the witness lives in the consumed prefix — the
decoder is NOT obliged to detect a collision and may keep consuming,
LambdaAuth's mechanization-found correction), completeness of the
decoder over the extractor stream (whole and slice alike), slice–whole
agreement, and the complete-decode root reconstruction — the last one
collision-free: the decoder recomputed every address itself, so a
completed full-range decode determines its root outright.
-/

namespace Effects.Merkle

open Effects.Cas (Bytes)

variable {A : Type}

/-! ## Local list lemmas (absent from the pinned core) -/

private theorem list_take_take {α : Type _} :
    ∀ (xs : List α) (m n : Nat), m ≤ n → (xs.take n).take m = xs.take m
  | [], _, _, _ => by simp
  | _ :: _, 0, _, _ => by simp
  | x :: xs, m + 1, n + 1, h => by
    simp only [List.take_succ_cons]
    rw [list_take_take xs m n (by omega)]

private theorem list_drop_take {α : Type _} :
    ∀ (xs : List α) (n m : Nat), (xs.take n).drop m = (xs.drop m).take (n - m)
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | _ :: _, n + 1, 0 => by simp
  | x :: xs, n + 1, m + 1 => by
    simp only [List.take_succ_cons, List.drop_succ_cons]
    rw [list_drop_take xs n m]
    congr 1
    omega

private theorem getD_of_lt {α : Type _} (l : List α) (n : Nat) (d : α)
    (h : n < l.length) : l.getD n d = l[n] := by
  simp [List.getD, List.getElem?_eq_getElem h]

/-! ## Committed segments and honest frames -/

/-- The committed segment a frame covers. -/
def seg (base count : Nat) (chunks : List Bytes) : List Bytes :=
  (chunks.drop base).take count

theorem seg_length (base count : Nat) (chunks : List Bytes)
    (h : base + count ≤ chunks.length) :
    (seg base count chunks).length = count := by
  simp only [seg, List.length_take, List.length_drop]
  omega

theorem seg_singleton (base : Nat) (chunks : List Bytes)
    (h : base < chunks.length) :
    seg base 1 chunks = [chunks.getD base []] := by
  simp only [seg]
  rw [List.drop_eq_getElem_cons h, getD_of_lt chunks base [] h]
  rfl

/-- The root of a leaf-sized list. -/
theorem root_leaf (P : HP A) (base : Nat) (chunks : List Bytes)
    (h : chunks.length ≤ 1) :
    root P base chunks = P.H (.leaf base (chunks.headD [])) := by
  conv => lhs; rw [root.eq_def]
  rw [dif_pos h]

theorem seg_take (base count k : Nat) (chunks : List Bytes) (h : k ≤ count) :
    (seg base count chunks).take k = seg base k chunks := by
  simp only [seg]
  exact list_take_take _ k count h

theorem seg_drop (base count k : Nat) (chunks : List Bytes) :
    (seg base count chunks).drop k = seg (base + k) (count - k) chunks := by
  simp only [seg]
  rw [list_drop_take, List.drop_drop]

/-- A frame is honest for a committed list when its address is the root
of exactly its segment. -/
def FrameOk (P : HP A) (chunks : List Bytes) (f : Frame A) : Prop :=
  0 < f.count ∧ f.base + f.count ≤ chunks.length ∧
    f.expected = root P f.base (seg f.base f.count chunks)

def FramesOk (P : HP A) (chunks : List Bytes) (s : DState A) : Prop :=
  ∀ f ∈ s.stack, FrameOk P chunks f

/-- The decision-tag projection for the trace instances. -/
inductive DTag where
  | emitted
  | lengthValidated
  | rejectedNode
  deriving DecidableEq

def DDecision.tag : DDecision A → DTag
  | .emitted _ _ => .emitted
  | .lengthValidated => .lengthValidated
  | .rejectedNode => .rejectedNode

variable [DecidableEq A]

/-! ## MRK-008: the run is a pure fold — composition over concatenation -/

/-- Runs compose over input concatenation: transport fragmentation
below the parser cannot change any emission, rejection, or terminal. -/
theorem drun_append (D : DParams A) (s : DState A)
    (xs ys : List (DInput A)) :
    drun D s (xs ++ ys) =
      ((drun D (drun D s xs).1 ys).1,
        (drun D s xs).2 ++ (drun D (drun D s xs).1 ys).2) := by
  induction xs generalizing s with
  | nil => simp [drun]
  | cons i is ih => simp [drun, ih]

/-- A non-active step absorbs and decides nothing. -/
theorem dstep_absorb (D : DParams A) (s : DState A) (i : DInput A)
    (h : s.status ≠ .active) : dstep D s i = ⟨s, []⟩ := by
  obtain ⟨stack, status⟩ := s
  cases status with
  | active => exact absurd rfl h
  | rejected => rfl
  | done => rfl

/-- A non-active decoder absorbs everything and decides nothing. -/
theorem drun_absorb (D : DParams A) (s : DState A)
    (h : s.status ≠ .active) (inputs : List (DInput A)) :
    drun D s inputs = (s, []) := by
  induction inputs with
  | nil => rfl
  | cons i is ih => simp [drun, dstep_absorb D s i h, ih]

/-! ## The per-step gates -/

/-- Whether the pending input is entitled to emit: the machine is
active, the top frame is an in-range leaf frame, and the input is a
chunk whose leaf pre-image hashes to exactly the expected address. -/
def emissionEntitled (D : DParams A) (s : DState A) (i : DInput A) : Bool :=
  match s.status, s.stack, i with
  | .active, f :: _, .chunkNode c =>
    !decide (D.disjoint f) && decide (f.count ≤ 1) &&
      decide (D.P.H (.leaf f.base c) = f.expected)
  | _, _, _ => false

/-- Whether the pending input is entitled to validate the length: it is
entitled to emit AND the emitted chunk is the final one. -/
def lengthEntitled (D : DParams A) (s : DState A) (i : DInput A) : Bool :=
  emissionEntitled D s i &&
    (match s.stack with
     | f :: _ => decide (f.base + 1 = D.total)
     | [] => false)

/-- MRK-002, per-step half: no step emits without entitlement — the
emission gate is the verification. -/
theorem dstep_emits_only_entitled (D : DParams A) (s : DState A)
    (i : DInput A) (h : emissionEntitled D s i = false) :
    DTag.emitted ∉ ((dstep D s i).decisions.map DDecision.tag) := by
  obtain ⟨stack, status⟩ := s
  cases status with
  | rejected => simp [dstep]
  | done => simp [dstep]
  | active =>
    cases stack with
    | nil => simp [dstep]
    | cons f rest =>
      simp only [dstep]
      split
      · cases i <;> simp [rejectOut, DDecision.tag]
      · rename_i hd
        split
        · rename_i hc
          cases i with
          | chunkNode c =>
            dsimp only
            split
            · rename_i hh
              exfalso
              have hent : emissionEntitled D ⟨f :: rest, .active⟩
                  (.chunkNode c) = true := by
                simp [emissionEntitled, hd, hc, hh]
              rw [h] at hent
              exact Bool.false_ne_true hent
            · simp [rejectOut, DDecision.tag]
          | parentNode l r => simp [rejectOut, DDecision.tag]
          | skipNode => simp [rejectOut, DDecision.tag]
        · cases i with
          | parentNode l r =>
            dsimp only
            split
            · simp
            · simp [rejectOut, DDecision.tag]
          | chunkNode c => simp [rejectOut, DDecision.tag]
          | skipNode => simp [rejectOut, DDecision.tag]

/-- MRK-003, per-step half: no step validates the length without
final-chunk entitlement — length is observable only through the final
chunk's own validation. -/
theorem dstep_length_only_final (D : DParams A) (s : DState A)
    (i : DInput A) (h : lengthEntitled D s i = false) :
    DTag.lengthValidated ∉ ((dstep D s i).decisions.map DDecision.tag) := by
  obtain ⟨stack, status⟩ := s
  cases status with
  | rejected => simp [dstep]
  | done => simp [dstep]
  | active =>
    cases stack with
    | nil => simp [dstep]
    | cons f rest =>
      simp only [dstep]
      split
      · cases i <;> simp [rejectOut, DDecision.tag]
      · rename_i hd
        split
        · rename_i hc
          cases i with
          | chunkNode c =>
            dsimp only
            split
            · rename_i hh
              split
              · rename_i hfin
                exfalso
                have hent : lengthEntitled D ⟨f :: rest, .active⟩
                    (.chunkNode c) = true := by
                  simp [lengthEntitled, emissionEntitled, hd, hc, hh, hfin]
                rw [h] at hent
                exact Bool.false_ne_true hent
              · simp [DDecision.tag]
            · simp [rejectOut, DDecision.tag]
          | parentNode l r => simp [rejectOut, DDecision.tag]
          | skipNode => simp [rejectOut, DDecision.tag]
        · cases i with
          | parentNode l r =>
            dsimp only
            split
            · simp
            · simp [rejectOut, DDecision.tag]
          | chunkNode c => simp [rejectOut, DDecision.tag]
          | skipNode => simp [rejectOut, DDecision.tag]

/-! ## MRK-002, run level: emission soundness against a committed list -/

/-- One step preserves frame honesty and emits only committed chunks —
or exhibits a collision. -/
theorem dstep_sound (D : DParams A) (chunks : List Bytes)
    (s : DState A) (i : DInput A) (hok : FramesOk D.P chunks s) :
    (FramesOk D.P chunks (dstep D s i).state ∧
      ∀ j b, DDecision.emitted j b ∈ (dstep D s i).decisions →
        b = chunks.getD j []) ∨ Collision D.P := by
  obtain ⟨stack, status⟩ := s
  cases status with
  | rejected => exact Or.inl ⟨hok, by simp [dstep]⟩
  | done => exact Or.inl ⟨hok, by simp [dstep]⟩
  | active =>
    cases stack with
    | nil => exact Or.inl ⟨hok, by simp [dstep]⟩
    | cons f rest =>
      have hfok : FrameOk D.P chunks f := hok f (List.mem_cons_self ..)
      have hrestOk : ∀ g ∈ rest, FrameOk D.P chunks g := fun g hg =>
        hok g (List.mem_cons_of_mem _ hg)
      obtain ⟨hpos, hbound, hexp⟩ := hfok
      simp only [dstep]
      split
      · -- disjoint frame
        cases i with
        | skipNode =>
          exact Or.inl ⟨fun g hg => hrestOk g hg, by simp⟩
        | parentNode l r =>
          exact Or.inl ⟨fun g hg => hok g hg, by simp [rejectOut]⟩
        | chunkNode c =>
          exact Or.inl ⟨fun g hg => hok g hg, by simp [rejectOut]⟩
      · rename_i hd
        split
        · -- leaf frame
          rename_i hc
          have hcount1 : f.count = 1 := by omega
          have hbase : f.base < chunks.length := by omega
          have hexp' : f.expected =
              D.P.H (.leaf f.base (chunks.getD f.base [])) := by
            rw [hexp, hcount1, seg_singleton f.base chunks hbase,
              root_leaf D.P f.base _ (by simp)]
            rfl
          cases i with
          | chunkNode c =>
            dsimp only
            split
            · rename_i hh
              by_cases hpre : (Pre.leaf f.base c : Pre A) =
                  .leaf f.base (chunks.getD f.base [])
              · have hb : c = chunks.getD f.base [] := by
                  injection hpre
                refine Or.inl ⟨fun g hg => hrestOk g hg, ?_⟩
                intro j b hmem
                split at hmem
                · simp only [List.mem_cons, List.not_mem_nil,
                    or_false] at hmem
                  rcases hmem with h1 | h1
                  · injection h1 with hj hbc
                    subst hj
                    subst hbc
                    exact hb
                  · exact nomatch h1
                · simp only [List.mem_cons, List.not_mem_nil,
                    or_false] at hmem
                  injection hmem with hj hbc
                  subst hj
                  subst hbc
                  exact hb
              · exact Or.inr ⟨_, _, hpre, hh.trans hexp'⟩
            · exact Or.inl ⟨fun g hg => hok g hg, by simp [rejectOut]⟩
          | parentNode l r =>
            exact Or.inl ⟨fun g hg => hok g hg, by simp [rejectOut]⟩
          | skipNode =>
            exact Or.inl ⟨fun g hg => hok g hg, by simp [rejectOut]⟩
        · -- interior frame
          rename_i hc
          have hlen2 : ¬ (seg f.base f.count chunks).length ≤ 1 := by
            rw [seg_length _ _ _ hbound]
            omega
          have hsplit := root_split D.P f.base (seg f.base f.count chunks) hlen2
          rw [seg_length _ _ _ hbound] at hsplit
          have hklt : pow2Below f.count < f.count :=
            pow2Below_lt f.count (by omega)
          have hkpos : 0 < pow2Below f.count := pow2Below_pos f.count
          rw [seg_take _ _ _ _ (by omega), seg_drop] at hsplit
          cases i with
          | parentNode l r =>
            dsimp only
            split
            · rename_i hh
              by_cases hpre : (Pre.parent l r : Pre A) =
                  .parent
                    (root D.P f.base (seg f.base (pow2Below f.count) chunks))
                    (root D.P (f.base + pow2Below f.count)
                      (seg (f.base + pow2Below f.count)
                        (f.count - pow2Below f.count) chunks))
              · rw [Pre.parent.injEq] at hpre
                obtain ⟨hl, hr⟩ := hpre
                refine Or.inl ⟨?_, by simp⟩
                intro g hg
                simp only [List.mem_cons] at hg
                rcases hg with hgl | hgr | hgrest
                · subst hgl
                  refine ⟨hkpos, ?_, hl⟩
                  show f.base + pow2Below f.count ≤ chunks.length
                  omega
                · subst hgr
                  refine ⟨?_, ?_, hr⟩
                  · show 0 < f.count - pow2Below f.count
                    omega
                  · show f.base + pow2Below f.count +
                      (f.count - pow2Below f.count) ≤ chunks.length
                    omega
                · exact hrestOk g hgrest
              · exact Or.inr ⟨_, _, hpre, hh.trans (hexp.trans hsplit)⟩
            · exact Or.inl ⟨fun g hg => hok g hg, by simp [rejectOut]⟩
          | chunkNode c =>
            exact Or.inl ⟨fun g hg => hok g hg, by simp [rejectOut]⟩
          | skipNode =>
            exact Or.inl ⟨fun g hg => hok g hg, by simp [rejectOut]⟩

/-- MRK-002, run level: against a committed list whose segments the
stack honestly expects, every emission of the whole run matches the
committed chunk at its index — or a collision witness exists. The
disjunction is OUTSIDE the quantifier: once a collision occurred in
the consumed prefix, later emissions are unconstrained (the decoder
cannot detect the collision and keeps consuming). -/
theorem drun_emissions_sound (D : DParams A) (chunks : List Bytes) :
    ∀ (inputs : List (DInput A)) (s : DState A),
      FramesOk D.P chunks s →
      ((∀ j b, DDecision.emitted j b ∈ (drun D s inputs).2 →
        b = chunks.getD j []) ∨ Collision D.P)
  | [], s, _ => Or.inl (by simp [drun])
  | i :: is, s, hok => by
    rcases dstep_sound D chunks s i hok with ⟨hnext, hstep⟩ | hcol
    · rcases drun_emissions_sound D chunks is (dstep D s i).state hnext with
        hrest | hcol
      · refine Or.inl ?_
        intro j b hmem
        simp only [drun, List.mem_append] at hmem
        rcases hmem with hmem | hmem
        · exact hstep j b hmem
        · exact hrest j b hmem
      · exact Or.inr hcol
    · exact Or.inr hcol

/-! ## Completeness over the extractor, whole and slice alike -/

/-- The honest decisions one subtree's stream produces. -/
def honestDecs (D : DParams A) (base : Nat) (chunks : List Bytes) :
    List (DDecision A) :=
  if base + chunks.length ≤ D.lo ∨ D.hi ≤ base then []
  else if _h : chunks.length ≤ 1 then
    if base + 1 = D.total then
      [.emitted base (chunks.headD []), .lengthValidated]
    else [.emitted base (chunks.headD [])]
  else
    honestDecs D base (chunks.take (pow2Below chunks.length)) ++
      honestDecs D (base + pow2Below chunks.length)
        (chunks.drop (pow2Below chunks.length))
termination_by chunks.length
decreasing_by
  · have hk := pow2Below_lt chunks.length (by omega)
    simp only [List.length_take]
    omega
  · have hk := pow2Below_pos chunks.length
    simp only [List.length_drop]
    omega

section SplitLemmas

omit [DecidableEq A] in
theorem genStream_skip (P : HP A) (lo hi base : Nat) (chunks : List Bytes)
    (hd : base + chunks.length ≤ lo ∨ hi ≤ base) :
    genStream P lo hi base chunks = [.skipNode] := by
  conv => lhs; rw [genStream.eq_def]
  rw [if_pos hd]

omit [DecidableEq A] in
theorem genStream_leaf (P : HP A) (lo hi base : Nat) (chunks : List Bytes)
    (hd : ¬ (base + chunks.length ≤ lo ∨ hi ≤ base))
    (h1 : chunks.length ≤ 1) :
    genStream P lo hi base chunks = [.chunkNode (chunks.headD [])] := by
  conv => lhs; rw [genStream.eq_def]
  rw [if_neg hd, dif_pos h1]

omit [DecidableEq A] in
theorem genStream_node (P : HP A) (lo hi base : Nat) (chunks : List Bytes)
    (hd : ¬ (base + chunks.length ≤ lo ∨ hi ≤ base))
    (h1 : ¬ chunks.length ≤ 1) :
    genStream P lo hi base chunks =
      .parentNode (root P base (chunks.take (pow2Below chunks.length)))
          (root P (base + pow2Below chunks.length)
            (chunks.drop (pow2Below chunks.length))) ::
        (genStream P lo hi base (chunks.take (pow2Below chunks.length)) ++
          genStream P lo hi (base + pow2Below chunks.length)
            (chunks.drop (pow2Below chunks.length))) := by
  conv => lhs; rw [genStream.eq_def]
  rw [if_neg hd, dif_neg h1]

omit [DecidableEq A] in
theorem honestDecs_skip (D : DParams A) (base : Nat) (chunks : List Bytes)
    (hd : base + chunks.length ≤ D.lo ∨ D.hi ≤ base) :
    honestDecs D base chunks = [] := by
  conv => lhs; rw [honestDecs.eq_def]
  rw [if_pos hd]

omit [DecidableEq A] in
theorem honestDecs_leaf (D : DParams A) (base : Nat) (chunks : List Bytes)
    (hd : ¬ (base + chunks.length ≤ D.lo ∨ D.hi ≤ base))
    (h1 : chunks.length ≤ 1) :
    honestDecs D base chunks =
      if base + 1 = D.total then
        [.emitted base (chunks.headD []), .lengthValidated]
      else [.emitted base (chunks.headD [])] := by
  conv => lhs; rw [honestDecs.eq_def]
  rw [if_neg hd, dif_pos h1]

omit [DecidableEq A] in
theorem honestDecs_node (D : DParams A) (base : Nat) (chunks : List Bytes)
    (hd : ¬ (base + chunks.length ≤ D.lo ∨ D.hi ≤ base))
    (h1 : ¬ chunks.length ≤ 1) :
    honestDecs D base chunks =
      honestDecs D base (chunks.take (pow2Below chunks.length)) ++
        honestDecs D (base + pow2Below chunks.length)
          (chunks.drop (pow2Below chunks.length)) := by
  conv => lhs; rw [honestDecs.eq_def]
  rw [if_neg hd, dif_neg h1]

omit [DecidableEq A] in
theorem rangedEmissions_skip (lo hi base : Nat) (chunks : List Bytes)
    (hd : base + chunks.length ≤ lo ∨ hi ≤ base) :
    rangedEmissions lo hi base chunks = [] := by
  conv => lhs; rw [rangedEmissions.eq_def]
  rw [if_pos hd]

omit [DecidableEq A] in
theorem rangedEmissions_leaf (lo hi base : Nat) (chunks : List Bytes)
    (hd : ¬ (base + chunks.length ≤ lo ∨ hi ≤ base))
    (h1 : chunks.length ≤ 1) :
    rangedEmissions lo hi base chunks = [(base, chunks.headD [])] := by
  conv => lhs; rw [rangedEmissions.eq_def]
  rw [if_neg hd, dif_pos h1]

omit [DecidableEq A] in
theorem rangedEmissions_node (lo hi base : Nat) (chunks : List Bytes)
    (hd : ¬ (base + chunks.length ≤ lo ∨ hi ≤ base))
    (h1 : ¬ chunks.length ≤ 1) :
    rangedEmissions lo hi base chunks =
      rangedEmissions lo hi base (chunks.take (pow2Below chunks.length)) ++
        rangedEmissions lo hi (base + pow2Below chunks.length)
          (chunks.drop (pow2Below chunks.length)) := by
  conv => lhs; rw [rangedEmissions.eq_def]
  rw [if_neg hd, dif_neg h1]

end SplitLemmas

/-- The honest run: from a frame honestly expecting a subtree's root,
the extractor's stream is consumed exactly — the frame pops, the
subtree's honest decisions are emitted, and the run continues. The
statement threads a continuation, so the node case composes without a
barrier; whole decodes and slices are the same theorem at different
ranges. -/
theorem drun_genStream (D : DParams A) :
    ∀ (chunks : List Bytes) (base : Nat) (rest : List (Frame A))
      (more : List (DInput A)), 0 < chunks.length →
      drun D ⟨⟨root D.P base chunks, base, chunks.length⟩ :: rest, .active⟩
          (genStream D.P D.lo D.hi base chunks ++ more) =
        ((drun D (popped rest) more).1,
          honestDecs D base chunks ++ (drun D (popped rest) more).2) := by
  intro chunks
  induction hn : chunks.length using Nat.strongRecOn
    generalizing chunks with
  | ind n ih =>
  intro base rest more hpos
  subst hn
  by_cases hd : base + chunks.length ≤ D.lo ∨ D.hi ≤ base
  · rw [genStream_skip D.P D.lo D.hi base chunks hd,
      honestDecs_skip D base chunks hd]
    have hdisj : D.disjoint ⟨root D.P base chunks, base, chunks.length⟩ := hd
    simp [drun, dstep, hdisj]
  · by_cases h1 : chunks.length ≤ 1
    · rw [genStream_leaf D.P D.lo D.hi base chunks hd h1,
        honestDecs_leaf D base chunks hd h1]
      have hndisj :
          ¬ D.disjoint ⟨root D.P base chunks, base, chunks.length⟩ := hd
      have hh : D.P.H (.leaf base (chunks.headD [])) =
          root D.P base chunks := (root_leaf D.P base chunks h1).symm
      have hstep : dstep D
          ⟨⟨root D.P base chunks, base, chunks.length⟩ :: rest, .active⟩
          (.chunkNode (chunks.headD [])) =
          ⟨popped rest,
            if base + 1 = D.total then
              [.emitted base (chunks.headD []), .lengthValidated]
            else [.emitted base (chunks.headD [])]⟩ := by
        dsimp only [dstep]
        rw [if_neg hndisj, if_pos h1, if_pos hh]
      simp only [List.singleton_append, drun, hstep]
    · rw [genStream_node D.P D.lo D.hi base chunks hd h1,
        honestDecs_node D base chunks hd h1]
      have hndisj :
          ¬ D.disjoint ⟨root D.P base chunks, base, chunks.length⟩ := hd
      have hk_lt := pow2Below_lt chunks.length (by omega)
      have hk_pos := pow2Below_pos chunks.length
      have hsplit := root_split D.P base chunks h1
      have htake_len :
          (chunks.take (pow2Below chunks.length)).length =
            pow2Below chunks.length := by
        simp only [List.length_take]
        omega
      have hdrop_len :
          (chunks.drop (pow2Below chunks.length)).length =
            chunks.length - pow2Below chunks.length := by
        simp only [List.length_drop]
      -- one accepted parent step, then the two children in sequence
      have hstep : dstep D
          ⟨⟨root D.P base chunks, base, chunks.length⟩ :: rest, .active⟩
          (.parentNode (root D.P base (chunks.take (pow2Below chunks.length)))
            (root D.P (base + pow2Below chunks.length)
              (chunks.drop (pow2Below chunks.length)))) =
          ⟨⟨⟨root D.P base (chunks.take (pow2Below chunks.length)), base,
              pow2Below chunks.length⟩ ::
             ⟨root D.P (base + pow2Below chunks.length)
                (chunks.drop (pow2Below chunks.length)),
              base + pow2Below chunks.length,
              chunks.length - pow2Below chunks.length⟩ :: rest, .active⟩,
            []⟩ := by
        dsimp only [dstep]
        rw [if_neg hndisj, if_neg h1, if_pos hsplit.symm]
      rw [List.cons_append, List.append_assoc]
      simp only [drun, hstep]
      have ihL := ih (pow2Below chunks.length) (by omega)
        (chunks.take (pow2Below chunks.length)) htake_len base
        (⟨root D.P (base + pow2Below chunks.length)
            (chunks.drop (pow2Below chunks.length)),
          base + pow2Below chunks.length,
          chunks.length - pow2Below chunks.length⟩ :: rest)
        (genStream D.P D.lo D.hi (base + pow2Below chunks.length)
            (chunks.drop (pow2Below chunks.length)) ++ more)
        (by omega)
      rw [ihL]
      have hpopL : popped
          (⟨root D.P (base + pow2Below chunks.length)
              (chunks.drop (pow2Below chunks.length)),
            base + pow2Below chunks.length,
            chunks.length - pow2Below chunks.length⟩ :: rest) =
          ⟨⟨root D.P (base + pow2Below chunks.length)
              (chunks.drop (pow2Below chunks.length)),
            base + pow2Below chunks.length,
            chunks.length - pow2Below chunks.length⟩ :: rest, .active⟩ := by
        simp [popped]
      rw [hpopL]
      have ihR := ih (chunks.length - pow2Below chunks.length) (by omega)
        (chunks.drop (pow2Below chunks.length)) hdrop_len
        (base + pow2Below chunks.length) rest more (by omega)
      rw [ihR]
      simp [List.append_assoc]

/-! ## MRK-005: slice–whole agreement -/

/-- The emission pairs of a decision list. -/
def emissionsOf (ds : List (DDecision A)) : List (Nat × Bytes) :=
  ds.filterMap fun
    | .emitted j b => some (j, b)
    | _ => none

omit [DecidableEq A] in
theorem emissionsOf_append (ds₁ ds₂ : List (DDecision A)) :
    emissionsOf (ds₁ ++ ds₂) = emissionsOf ds₁ ++ emissionsOf ds₂ := by
  simp [emissionsOf]

omit [DecidableEq A] in
theorem emissionsOf_honestDecs (D : DParams A) :
    ∀ (chunks : List Bytes) (base : Nat),
      emissionsOf (honestDecs D base chunks) =
        rangedEmissions D.lo D.hi base chunks := by
  intro chunks
  induction hn : chunks.length using Nat.strongRecOn
    generalizing chunks with
  | ind n ih =>
  intro base
  subst hn
  by_cases hd : base + chunks.length ≤ D.lo ∨ D.hi ≤ base
  · rw [honestDecs_skip D base chunks hd, rangedEmissions_skip _ _ _ _ hd]
    rfl
  · by_cases h1 : chunks.length ≤ 1
    · rw [honestDecs_leaf D base chunks hd h1,
        rangedEmissions_leaf _ _ _ _ hd h1]
      split <;> simp [emissionsOf]
    · rw [honestDecs_node D base chunks hd h1,
        rangedEmissions_node _ _ _ _ hd h1, emissionsOf_append]
      have hk_lt := pow2Below_lt chunks.length (by omega)
      have hk_pos := pow2Below_pos chunks.length
      have htake_len :
          (chunks.take (pow2Below chunks.length)).length =
            pow2Below chunks.length := by
        simp only [List.length_take]
        omega
      have hdrop_len :
          (chunks.drop (pow2Below chunks.length)).length =
            chunks.length - pow2Below chunks.length := by
        simp only [List.length_drop]
      rw [ih (pow2Below chunks.length) (by omega) _ htake_len,
        ih (chunks.length - pow2Below chunks.length) (by omega) _ hdrop_len]

omit [DecidableEq A] in
/-- Every ranged emission's index lies in the subtree and in the range. -/
theorem rangedEmissions_indices (lo hi : Nat) :
    ∀ (chunks : List Bytes) (base : Nat) (p : Nat × Bytes),
      0 < chunks.length →
      p ∈ rangedEmissions lo hi base chunks →
      base ≤ p.1 ∧ p.1 < base + chunks.length ∧ lo ≤ p.1 ∧ p.1 < hi := by
  intro chunks
  induction hn : chunks.length using Nat.strongRecOn
    generalizing chunks with
  | ind n ih =>
  intro base p hpos hp
  subst hn
  by_cases hd : base + chunks.length ≤ lo ∨ hi ≤ base
  · rw [rangedEmissions_skip _ _ _ _ hd] at hp
    exact absurd hp (List.not_mem_nil)
  · by_cases h1 : chunks.length ≤ 1
    · rw [rangedEmissions_leaf _ _ _ _ hd h1] at hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      dsimp only
      omega
    · rw [rangedEmissions_node _ _ _ _ hd h1] at hp
      have hk_lt := pow2Below_lt chunks.length (by omega)
      have hk_pos := pow2Below_pos chunks.length
      have htake_len :
          (chunks.take (pow2Below chunks.length)).length =
            pow2Below chunks.length := by
        simp only [List.length_take]
        omega
      have hdrop_len :
          (chunks.drop (pow2Below chunks.length)).length =
            chunks.length - pow2Below chunks.length := by
        simp only [List.length_drop]
      rcases List.mem_append.mp hp with hp | hp
      · have := ih (pow2Below chunks.length) (by omega) _ htake_len base p
          (by omega) hp
        omega
      · have := ih (chunks.length - pow2Below chunks.length) (by omega) _
          hdrop_len (base + pow2Below chunks.length) p
          (by omega) hp
        omega

omit [DecidableEq A] in
/-- A range covering the whole subtree emits everything: the range
bounds are invisible. -/
theorem rangedEmissions_covering :
    ∀ (chunks : List Bytes) (lo hi lo' hi' base : Nat),
      0 < chunks.length →
      lo ≤ base → base + chunks.length ≤ hi →
      lo' ≤ base → base + chunks.length ≤ hi' →
      rangedEmissions lo hi base chunks =
        rangedEmissions lo' hi' base chunks := by
  intro chunks
  induction hn : chunks.length using Nat.strongRecOn
    generalizing chunks with
  | ind n ih =>
  intro lo hi lo' hi' base hpos hlo hhi hlo' hhi'
  subst hn
  have hd : ¬ (base + chunks.length ≤ lo ∨ hi ≤ base) := by omega
  have hd' : ¬ (base + chunks.length ≤ lo' ∨ hi' ≤ base) := by omega
  by_cases h1 : chunks.length ≤ 1
  · rw [rangedEmissions_leaf _ _ _ _ hd h1,
      rangedEmissions_leaf _ _ _ _ hd' h1]
  · rw [rangedEmissions_node _ _ _ _ hd h1,
      rangedEmissions_node _ _ _ _ hd' h1]
    have hk_lt := pow2Below_lt chunks.length (by omega)
    have hk_pos := pow2Below_pos chunks.length
    have htake_len :
        (chunks.take (pow2Below chunks.length)).length =
          pow2Below chunks.length := by
      simp only [List.length_take]
      omega
    have hdrop_len :
        (chunks.drop (pow2Below chunks.length)).length =
          chunks.length - pow2Below chunks.length := by
      simp only [List.length_drop]
    rw [ih (pow2Below chunks.length) (by omega) _ htake_len lo hi lo' hi'
        base (by omega) hlo (by omega) hlo' (by omega),
      ih (chunks.length - pow2Below chunks.length) (by omega) _ hdrop_len
        lo hi lo' hi' (base + pow2Below chunks.length) (by omega)
        (by omega) (by omega)
        (by omega) (by omega)]

omit [DecidableEq A] in
/-- The slice is the whole, filtered: MRK-005's law over arbitrary
ranges. -/
theorem rangedEmissions_eq_filter :
    ∀ (chunks : List Bytes) (lo hi base : Nat), 0 < chunks.length →
      rangedEmissions lo hi base chunks =
        (rangedEmissions 0 (base + chunks.length) base chunks).filter
          (fun p => decide (lo ≤ p.1) && decide (p.1 < hi)) := by
  intro chunks
  induction hn : chunks.length using Nat.strongRecOn
    generalizing chunks with
  | ind n ih =>
  intro lo hi base hpos
  subst hn
  by_cases hd : base + chunks.length ≤ lo ∨ hi ≤ base
  · rw [rangedEmissions_skip _ _ _ _ hd]
    symm
    rw [List.filter_eq_nil_iff]
    intro p hp
    have hb := rangedEmissions_indices 0 (base + chunks.length) chunks base p
      hpos hp
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    omega
  · by_cases h1 : chunks.length ≤ 1
    · have hd0 : ¬ (base + chunks.length ≤ 0 ∨ base + chunks.length ≤ base) := by
        omega
      rw [rangedEmissions_leaf _ _ _ _ hd h1,
        rangedEmissions_leaf _ _ _ _ hd0 h1]
      have hin : lo ≤ base ∧ base < hi := by omega
      simp [hin.1, hin.2]
    · have hd0 : ¬ (base + chunks.length ≤ 0 ∨ base + chunks.length ≤ base) := by
        omega
      rw [rangedEmissions_node _ _ _ _ hd h1,
        rangedEmissions_node _ _ _ _ hd0 h1, List.filter_append]
      have hk_lt := pow2Below_lt chunks.length (by omega)
      have hk_pos := pow2Below_pos chunks.length
      have htake_len :
          (chunks.take (pow2Below chunks.length)).length =
            pow2Below chunks.length := by
        simp only [List.length_take]
        omega
      have hdrop_len :
          (chunks.drop (pow2Below chunks.length)).length =
            chunks.length - pow2Below chunks.length := by
        simp only [List.length_drop]
      have hcovL := rangedEmissions_covering
        (chunks.take (pow2Below chunks.length)) 0 (base + chunks.length)
        0 (base + pow2Below chunks.length) base
        (by simp only [List.length_take]; omega)
        (by omega) (by rw [htake_len]; omega)
        (by omega) (by rw [htake_len]; omega)
      have hcovR := rangedEmissions_covering
        (chunks.drop (pow2Below chunks.length)) 0 (base + chunks.length)
        0 (base + pow2Below chunks.length +
            (chunks.length - pow2Below chunks.length))
        (base + pow2Below chunks.length)
        (by simp only [List.length_drop]; omega)
        (by omega) (by rw [hdrop_len]; omega)
        (by omega) (by rw [hdrop_len]; omega)
      rw [hcovL, hcovR,
        ih (pow2Below chunks.length) (by omega) _ htake_len lo hi base
          (by omega),
        ih (chunks.length - pow2Below chunks.length) (by omega) _ hdrop_len
          lo hi (base + pow2Below chunks.length)
          (by omega)]

/-- MRK-005 at the machine: the emissions of a slice run over its
extractor stream are exactly the whole run's emissions filtered to the
range. -/
theorem slice_whole_agreement (P : HP A) (lo hi : Nat)
    (chunks : List Bytes) (hpos : 0 < chunks.length) :
    emissionsOf (drun ⟨P, chunks.length, root P 0 chunks, lo, hi⟩
        (initState ⟨P, chunks.length, root P 0 chunks, lo, hi⟩)
        (genStream P lo hi 0 chunks)).2 =
      (emissionsOf (drun ⟨P, chunks.length, root P 0 chunks, 0, chunks.length⟩
          (initState ⟨P, chunks.length, root P 0 chunks, 0, chunks.length⟩)
          (genStream P 0 chunks.length 0 chunks)).2).filter
        (fun p => decide (lo ≤ p.1) && decide (p.1 < hi)) := by
  have hL := drun_genStream ⟨P, chunks.length, root P 0 chunks, lo, hi⟩
    chunks 0 [] [] hpos
  have hW := drun_genStream
    ⟨P, chunks.length, root P 0 chunks, 0, chunks.length⟩
    chunks 0 [] [] hpos
  simp only [List.append_nil] at hL hW
  simp only [initState]
  rw [hL, hW]
  simp only [drun, List.append_nil, emissionsOf_honestDecs]
  have := rangedEmissions_eq_filter chunks lo hi 0 hpos
  simpa using this

/-! ## MRK-004: a complete decode determines its root -/

theorem drun_empty_active (D : DParams A) (inputs : List (DInput A)) :
    drun D ⟨[], .active⟩ inputs = (⟨[], .active⟩, []) := by
  induction inputs with
  | nil => rfl
  | cons i is ih => simp [drun, dstep, ih]

omit [DecidableEq A] in
private theorem emissionsOf_emitArm (D : DParams A) (f : Frame A)
    (c : Bytes) (ds : List (DDecision A)) :
    emissionsOf ((if f.base + 1 = D.total then
        [DDecision.emitted f.base c, DDecision.lengthValidated]
      else [DDecision.emitted f.base c]) ++ ds) =
      (f.base, c) :: emissionsOf ds := by
  split <;> simp [emissionsOf]

/-- Machine runs reaching done decompose into the consumption
relation: the consumed prefix is derivable, frame by frame. -/
theorem drun_done_consumesStack (D : DParams A) :
    ∀ (inputs : List (DInput A)) (fs : List (Frame A)),
      (drun D ⟨fs, .active⟩ inputs).1.status = .done →
      ∃ used extra, inputs = used ++ extra ∧
        ConsumesStack D fs used
          (emissionsOf (drun D ⟨fs, .active⟩ inputs).2)
  | [], fs, hdone => by simp [drun] at hdone
  | i :: is, fs, hdone => by
    cases fs with
    | nil =>
      rw [drun_empty_active D (i :: is)] at hdone
      exact absurd hdone (by simp)
    | cons f rest =>
      by_cases hd : D.disjoint f
      · cases i with
        | skipNode =>
          have hstep : dstep D ⟨f :: rest, .active⟩ .skipNode =
              ⟨popped rest, []⟩ := by
            dsimp only [dstep]
            rw [if_pos hd]
          simp only [drun, hstep, List.nil_append] at hdone ⊢
          cases rest with
          | nil =>
            rw [show popped ([] : List (Frame A)) = ⟨[], .done⟩ from rfl]
              at hdone ⊢
            rw [drun_absorb D ⟨[], .done⟩ (by simp) is] at hdone ⊢
            refine ⟨[.skipNode], is, rfl, ?_⟩
            simpa [emissionsOf] using
              (ConsumesStack.cons (Consumes.skip hd) ConsumesStack.nil :
                ConsumesStack D [f] ([.skipNode] ++ []) ([] ++ []))
          | cons g gs =>
            rw [show popped (g :: gs) = ⟨g :: gs, .active⟩ from by
              simp [popped]] at hdone ⊢
            obtain ⟨used, extra, hin, hcs⟩ :=
              drun_done_consumesStack D is (g :: gs) hdone
            refine ⟨.skipNode :: used, extra, by simp [hin], ?_⟩
            simpa using ConsumesStack.cons (Consumes.skip hd) hcs
        | parentNode l r =>
          have hstep : dstep D ⟨f :: rest, .active⟩ (.parentNode l r) =
              rejectOut ⟨f :: rest, .active⟩ := by
            dsimp only [dstep]
            rw [if_pos hd]
          simp only [drun, hstep, rejectOut] at hdone
          rw [drun_absorb D _ (by simp) is] at hdone
          exact absurd hdone (by simp)
        | chunkNode c =>
          have hstep : dstep D ⟨f :: rest, .active⟩ (.chunkNode c) =
              rejectOut ⟨f :: rest, .active⟩ := by
            dsimp only [dstep]
            rw [if_pos hd]
          simp only [drun, hstep, rejectOut] at hdone
          rw [drun_absorb D _ (by simp) is] at hdone
          exact absurd hdone (by simp)
      · by_cases hc : f.count ≤ 1
        · cases i with
          | chunkNode c =>
            by_cases hh : D.P.H (.leaf f.base c) = f.expected
            · have hstep : dstep D ⟨f :: rest, .active⟩ (.chunkNode c) =
                  ⟨popped rest,
                    if f.base + 1 = D.total then
                      [.emitted f.base c, .lengthValidated]
                    else [.emitted f.base c]⟩ := by
                dsimp only [dstep]
                rw [if_neg hd, if_pos hc, if_pos hh]
              simp only [drun, hstep] at hdone ⊢
              rw [emissionsOf_emitArm]
              cases rest with
              | nil =>
                rw [show popped ([] : List (Frame A)) = ⟨[], .done⟩ from rfl]
                  at hdone ⊢
                rw [drun_absorb D ⟨[], .done⟩ (by simp) is] at hdone ⊢
                refine ⟨[.chunkNode c], is, rfl, ?_⟩
                simpa [emissionsOf] using
                  (ConsumesStack.cons (Consumes.leaf hd hc hh)
                      ConsumesStack.nil :
                    ConsumesStack D [f] ([.chunkNode c] ++ [])
                      ([(f.base, c)] ++ []))
              | cons g gs =>
                rw [show popped (g :: gs) = ⟨g :: gs, .active⟩ from by
                  simp [popped]] at hdone ⊢
                obtain ⟨used, extra, hin, hcs⟩ :=
                  drun_done_consumesStack D is (g :: gs) hdone
                refine ⟨.chunkNode c :: used, extra, by simp [hin], ?_⟩
                simpa using
                  ConsumesStack.cons (Consumes.leaf hd hc hh) hcs
            · have hstep : dstep D ⟨f :: rest, .active⟩ (.chunkNode c) =
                  rejectOut ⟨f :: rest, .active⟩ := by
                dsimp only [dstep]
                rw [if_neg hd, if_pos hc, if_neg hh]
              simp only [drun, hstep, rejectOut] at hdone
              rw [drun_absorb D _ (by simp) is] at hdone
              exact absurd hdone (by simp)
          | parentNode l r =>
            have hstep : dstep D ⟨f :: rest, .active⟩ (.parentNode l r) =
                rejectOut ⟨f :: rest, .active⟩ := by
              dsimp only [dstep]
              rw [if_neg hd, if_pos hc]
            simp only [drun, hstep, rejectOut] at hdone
            rw [drun_absorb D _ (by simp) is] at hdone
            exact absurd hdone (by simp)
          | skipNode =>
            have hstep : dstep D ⟨f :: rest, .active⟩ .skipNode =
                rejectOut ⟨f :: rest, .active⟩ := by
              dsimp only [dstep]
              rw [if_neg hd, if_pos hc]
            simp only [drun, hstep, rejectOut] at hdone
            rw [drun_absorb D _ (by simp) is] at hdone
            exact absurd hdone (by simp)
        · cases i with
          | parentNode l r =>
            by_cases hh : D.P.H (.parent l r) = f.expected
            · have hstep : dstep D ⟨f :: rest, .active⟩ (.parentNode l r) =
                  ⟨⟨⟨l, f.base, pow2Below f.count⟩ ::
                     ⟨r, f.base + pow2Below f.count,
                       f.count - pow2Below f.count⟩ :: rest, .active⟩,
                    []⟩ := by
                dsimp only [dstep]
                rw [if_neg hd, if_neg hc, if_pos hh]
              simp only [drun, hstep, List.nil_append] at hdone ⊢
              obtain ⟨used, extra, hin, hcs⟩ :=
                drun_done_consumesStack D is
                  (⟨l, f.base, pow2Below f.count⟩ ::
                    ⟨r, f.base + pow2Below f.count,
                      f.count - pow2Below f.count⟩ :: rest) hdone
              generalize hes : emissionsOf (drun D ⟨⟨l, f.base, pow2Below f.count⟩ :: ⟨r, f.base + pow2Below f.count, f.count - pow2Below f.count⟩ :: rest, .active⟩ is).2 = es at hcs ⊢
              rcases hcs with _ | @⟨_, _, in₁, in₂, es₁, es₂, h₁, hcs₂⟩
              rcases hcs₂ with _ | @⟨_, _, in₃, in₄, es₃, es₄, h₃, h₄⟩
              refine ⟨.parentNode l r :: ((in₁ ++ in₃) ++ in₄), extra,
                ?_, ?_⟩
              · simp [hin, List.append_assoc]
              · simpa [List.append_assoc] using
                  ConsumesStack.cons (Consumes.node hd hc hh h₁ h₃) h₄
            · have hstep : dstep D ⟨f :: rest, .active⟩ (.parentNode l r) =
                  rejectOut ⟨f :: rest, .active⟩ := by
                dsimp only [dstep]
                rw [if_neg hd, if_neg hc, if_neg hh]
              simp only [drun, hstep, rejectOut] at hdone
              rw [drun_absorb D _ (by simp) is] at hdone
              exact absurd hdone (by simp)
          | chunkNode c =>
            have hstep : dstep D ⟨f :: rest, .active⟩ (.chunkNode c) =
                rejectOut ⟨f :: rest, .active⟩ := by
              dsimp only [dstep]
              rw [if_neg hd, if_neg hc]
            simp only [drun, hstep, rejectOut] at hdone
            rw [drun_absorb D _ (by simp) is] at hdone
            exact absurd hdone (by simp)
          | skipNode =>
            have hstep : dstep D ⟨f :: rest, .active⟩ .skipNode =
                rejectOut ⟨f :: rest, .active⟩ := by
              dsimp only [dstep]
              rw [if_neg hd, if_neg hc]
            simp only [drun, hstep, rejectOut] at hdone
            rw [drun_absorb D _ (by simp) is] at hdone
            exact absurd hdone (by simp)

/-- Full-range consumptions reconstruct: the consumed emissions count
the frame's chunks exactly, and the frame's address IS the root of the
emitted bytes. Collision-free — the decoder recomputed everything. -/
theorem consumes_length_root (D : DParams A) (hlo : D.lo = 0)
    (hhi : D.total ≤ D.hi) :
    ∀ {f : Frame A} {ins : List (DInput A)} {es : List (Nat × Bytes)},
      Consumes D f ins es → 0 < f.count → f.base + f.count ≤ D.total →
      es.length = f.count ∧
        f.expected = root D.P f.base (es.map (·.2)) := by
  intro f ins es h
  induction h with
  | skip hd =>
    intro hpos hbound
    exfalso
    rcases hd with hd | hd <;> omega
  | leaf hd hc hh =>
    intro hpos hbound
    refine ⟨by simp; omega, ?_⟩
    rw [root_leaf _ _ _ (by simp)]
    simpa using hh.symm
  | node hd hc hh h₁ h₂ ih₁ ih₂ =>
    rename_i f' l r in₁ in₂ es₁ es₂
    intro hpos hbound
    have hk_lt := pow2Below_lt f'.count (by omega)
    have hk_pos := pow2Below_pos f'.count
    obtain ⟨hlen₁, hroot₁⟩ := ih₁ (by simpa using hk_pos) (by simp; omega)
    obtain ⟨hlen₂, hroot₂⟩ := ih₂ (by simp; omega) (by simp; omega)
    simp only at hlen₁ hroot₁ hlen₂ hroot₂
    have hlen : (es₁ ++ es₂).length = f'.count := by
      simp [hlen₁, hlen₂]
      omega
    refine ⟨hlen, ?_⟩
    have hmaplen : (es₁.map (·.2)).length = pow2Below f'.count := by
      simpa using hlen₁
    have hsplit := root_split D.P f'.base ((es₁ ++ es₂).map (·.2)) (by
      rw [List.length_map, hlen]
      omega)
    rw [List.length_map, hlen] at hsplit
    rw [hsplit, List.map_append,
      List.take_left' hmaplen, List.drop_left' hmaplen]
    rw [← hroot₁, ← hroot₂, ← hh]

/-- MRK-004: a completed full-range decode determines its root — the
expected root IS the root of the emitted bytes, with no collision
disjunct: the decoder recomputed every address itself. -/
theorem complete_decode_root (D : DParams A) (hlo : D.lo = 0)
    (hhi : D.total ≤ D.hi) (hpos : 0 < D.total)
    (inputs : List (DInput A))
    (hdone : (drun D (initState D) inputs).1.status = .done) :
    D.expectedRoot =
      root D.P 0 ((emissionsOf (drun D (initState D) inputs).2).map (·.2)) := by
  simp only [initState] at hdone ⊢
  obtain ⟨used, extra, hin, hcs⟩ :=
    drun_done_consumesStack D inputs [⟨D.expectedRoot, 0, D.total⟩] hdone
  generalize hes : emissionsOf
    (drun D ⟨[⟨D.expectedRoot, 0, D.total⟩], .active⟩ inputs).2 = es
    at hcs ⊢
  rcases hcs with _ | @⟨_, _, in₁, in₂, es₁, es₂, h₁, hnil⟩
  cases hnil
  have := (consumes_length_root D hlo hhi h₁ (by simpa using hpos)
    (by simp)).2
  simpa using this

/-- MRK-013 carrier: ranged stream generation is complete. For any
requested range, the honest extractor's stream runs the decoder to its
done status and emits exactly the owed ranged emissions — whose
indices are exactly the in-range tree positions and which agree with
the whole decode filtered to the range, by the standing
characterization lemmas. This is the server half: the reference
emitter behind the range-stream endpoint is honest by this theorem. -/
theorem ranged_generation_complete (P : HP A) (lo hi : Nat)
    (chunks : List Bytes) (hpos : 0 < chunks.length) :
    (drun ⟨P, chunks.length, root P 0 chunks, lo, hi⟩
        (initState ⟨P, chunks.length, root P 0 chunks, lo, hi⟩)
        (genStream P lo hi 0 chunks)).1.status = .done ∧
      emissionsOf (drun ⟨P, chunks.length, root P 0 chunks, lo, hi⟩
          (initState ⟨P, chunks.length, root P 0 chunks, lo, hi⟩)
          (genStream P lo hi 0 chunks)).2 =
        rangedEmissions lo hi 0 chunks := by
  have h := drun_genStream ⟨P, chunks.length, root P 0 chunks, lo, hi⟩
    chunks 0 [] [] hpos
  simp only [List.append_nil] at h
  simp only [initState]
  rw [h]
  constructor
  · simp [drun, popped]
  · rw [show (drun ⟨P, chunks.length, root P 0 chunks, lo, hi⟩
        (popped []) []).2 = [] from rfl]
    rw [List.append_nil]
    exact emissionsOf_honestDecs ⟨P, chunks.length, root P 0 chunks, lo, hi⟩
      chunks 0

/-- One frame's accepted consumption against the committed subtree it
claims: the emissions are the owed ranged emissions, or two distinct
pre-images with one address are exhibited. The walk compares the
consumption derivation with the committed tree level by level. -/
theorem consumes_binds_ranged (D : DParams A) :
    ∀ {f : Frame A} {ins : List (DInput A)} {es : List (Nat × Bytes)},
      Consumes D f ins es →
      ∀ (chunks : List Bytes), 0 < chunks.length →
      f.count = chunks.length →
      f.expected = root D.P f.base chunks →
      es = rangedEmissions D.lo D.hi f.base chunks ∨ Collision D.P := by
  intro f ins es h
  induction h with
  | @skip f hd =>
    intro chunks hpos hcount hroot
    left
    rw [rangedEmissions_skip D.lo D.hi f.base chunks (by
      simp only [DParams.disjoint] at hd
      omega)]
  | @leaf f c hd hc hh =>
    intro chunks hpos hcount hroot
    have h1 : chunks.length ≤ 1 := by omega
    have hleaf : root D.P f.base chunks =
        D.P.H (.leaf f.base (chunks.headD [])) := by
      conv => lhs; rw [root.eq_def]
      rw [dif_pos h1]
    by_cases hpre : (Pre.leaf f.base c : Pre A) =
        .leaf f.base (chunks.headD [])
    · left
      injection hpre with hbase hbytes
      rw [rangedEmissions_leaf D.lo D.hi f.base chunks (by
          simp only [DParams.disjoint] at hd
          omega) h1]
      rw [hbytes]
    · right
      exact ⟨_, _, hpre, hh.trans (hroot.trans hleaf)⟩
  | @node f l r in₁ in₂ es₁ es₂ hd hc hh h₁ h₂ ih₁ ih₂ =>
    intro chunks hpos hcount hroot
    have h1 : ¬ chunks.length ≤ 1 := by omega
    have hk_lt := pow2Below_lt chunks.length (by omega)
    have hk_pos := pow2Below_pos chunks.length
    have hkeq : pow2Below f.count = pow2Below chunks.length := by
      rw [hcount]
    rw [root_split D.P f.base chunks h1] at hroot
    by_cases hpre : (Pre.parent l r : Pre A) =
        .parent (root D.P f.base (chunks.take (pow2Below chunks.length)))
          (root D.P (f.base + pow2Below chunks.length)
            (chunks.drop (pow2Below chunks.length)))
    · injection hpre with hl hr
      have htake_len : (chunks.take (pow2Below chunks.length)).length =
          pow2Below chunks.length := by
        simp only [List.length_take]
        omega
      have hdrop_len : (chunks.drop (pow2Below chunks.length)).length =
          chunks.length - pow2Below chunks.length := by
        simp only [List.length_drop]
      have hbind₁ := ih₁ (chunks.take (pow2Below chunks.length))
        (by omega) (by simpa [htake_len] using hkeq)
        (by simpa using hl)
      have hbind₂ := ih₂ (chunks.drop (pow2Below chunks.length))
        (by omega) (by simp only [hdrop_len]; omega)
        (by simpa [hkeq] using hr)
      rcases hbind₁ with he₁ | hcol
      · rcases hbind₂ with he₂ | hcol
        · left
          rw [rangedEmissions_node D.lo D.hi f.base chunks (by
              simp only [DParams.disjoint] at hd
              omega) h1]
          simp only [hkeq] at he₂
          rw [he₁, he₂]
        · exact Or.inr hcol
      · exact Or.inr hcol
    · right
      exact ⟨_, _, hpre, hh.trans hroot⟩

/-- The judgment a runtime claims when it reports a root-checked
range: the decoder accepted the trace to its done status. -/
def PrefixAccepted [DecidableEq A] (D : DParams A)
    (inputs : List (DInput A)) : Prop :=
  (drun D (initState D) inputs).1.status = .done

/-- MRK-016 carrier — the adversarial ranged binding: ANY input trace
accepted for a root and range emits exactly the committed ranged
emissions at those positions, or the trace exhibits a computable hash
collision. Never a collision-resistance assumption; the
honest-generator half is `ranged_generation_complete`, a separate
theorem, and the expected root's provenance is the caller's declared
trust path — the theorem binds emissions to the root it was GIVEN. -/
theorem ranged_binding (D : DParams A) (chunks : List Bytes)
    (hroot : D.expectedRoot = root D.P 0 chunks)
    (htotal : D.total = chunks.length) (hpos : 0 < chunks.length)
    (inputs : List (DInput A))
    (hacc : PrefixAccepted D inputs) :
    emissionsOf (drun D (initState D) inputs).2 =
      rangedEmissions D.lo D.hi 0 chunks ∨ Collision D.P := by
  unfold PrefixAccepted at hacc
  simp only [initState] at hacc ⊢
  obtain ⟨used, extra, hin, hcs⟩ :=
    drun_done_consumesStack D inputs [⟨D.expectedRoot, 0, D.total⟩] hacc
  generalize hes : emissionsOf
    (drun D ⟨[⟨D.expectedRoot, 0, D.total⟩], .active⟩ inputs).2 = es
    at hcs ⊢
  rcases hcs with _ | @⟨_, _, in₁, in₂, es₁, es₂, h₁, hnil⟩
  cases hnil
  have := consumes_binds_ranged D h₁ chunks hpos (by simpa using htotal)
    (by simpa using hroot)
  simpa using this

end Effects.Merkle
