import Cas.Core.Canonicalize

/-!
# BREAKER attack on `EC1-T007` (`workshop/s1/T007.lean`), slice `EC1-S1`

Skill stage: `.claude/skills/lean/workflows/lean-assurance-review` — the target
is a landed proof reported `PROVED-WEAKER` (carrier) / "strictly stronger than
the DAG row and the scout" (theorem), so this is an assurance review run
adversarially.

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/attack-T007.lean
```

The carrier below is a VERBATIM re-declaration of `T007.lean`'s scratch carrier
(`BlockId`, `OpId`, `RawBlock`, `RawProgram`, `keys`, `RawBlock.rename`,
`applyRenaming`, `IsRenaming`, `AlphaEq`, `Renames`, `idx`, `canonId`,
`normalizeRaw`, `ProgramWF`). Nothing is imported from `T007.lean` — it is not a
Lake module — so every lemma is RE-DERIVED here.

## What does NOT survive

* §2 **the headline strengthening is not a strengthening.** `Renames` and
  `AlphaEq` are the SAME relation at this carrier (`renames_iff_alphaEq`), so
  `normalizeRaw_renames` is not "strictly stronger than the row"; for EVERY
  normalizer the two rows are inter-derivable
  (`row_over_renames_iff_row_over_alphaEq`). `applyRenaming` reads its function
  at finitely many points, and every injection is corrected to a bijection there
  by finitely many transpositions (`exists_perm_agreeing`). The target exhibits
  no pair separating them, and `no_pair_separates_renames_from_alphaEq` proves
  none exists.
* §3 **`normalizeRaw` reads an observable the declared carrier does not have.**
  `ALGEBRA.md:235` declares `blockTable` a "finite BlockId -> RawBlock map".
  Two duplicate-free programs with the same entry and the same finite map get
  DIFFERENT normal forms (`normalizeRaw_is_not_row_permutation_invariant`),
  because the normalizer is built from row ORDER. So `normalizeRaw` is not a
  function of the declared table, and `PROOF-DAG.md:100-102`'s declaration
  obligation "canonical ordering/normalization for rows and tables" is not
  merely unmet — row order is made LOAD-BEARING, the opposite. The shape the
  packet uses for that obligation (`EC1-T002`, `PROOF-DAG.md:190`, on the
  estate's `canonServices_perm_of_nodup_keys`) fails for this normalizer at a
  duplicate-free witness — the exact case `EC1-CE030` leaves standing.
* §4 `ProgramWF` is not the premise §8's laws need: two of its three clauses are
  droppable at witnesses (`dupKeys_still_renames`, `entryFree_still_renames`),
  and idempotence holds at three non-well-formed witnesses.
* §6 `free_namespace_refutes_the_row` does not refute THIS file's row:
  `renameOps swapOp two` is not `AlphaEq` to `two` (`opSwap_is_not_alphaEq`), so
  the theorem constrains a hypothetical alphaEq the file does not declare.

## What survives

* §1 the row itself re-derives independently (`normalizeRaw_alpha_recheck`) and
  is not vacuous.
* §5 `EC1-F01` (delete a target block) and `EC1-F03` (duplicate a block ID) do
  not touch the row; only §8's soundness law feels them, and it feels `F01`
  correctly (`dangle_not_renames`) — the `succsDeclared` clause IS necessary.
* §7 `preserve_keys_is_incompatible_with_the_row` survives strengthening: the
  obstruction still fires when `hpres` is restricted to WELL-FORMED programs
  (`preserve_keys_obstruction_survives_wf_restriction`), so no well-formedness
  premise rescues a key-preserving normalizer.
-/

namespace EffectCoreV1.AttackT007

/-! ## §0 — the target's carrier, re-declared verbatim -/

abbrev BlockId := Nat
abbrev OpId := String

structure RawBlock where
  op : OpId
  succs : List BlockId
  deriving DecidableEq

structure RawProgram where
  entry : BlockId
  blocks : List (BlockId × RawBlock)
  deriving DecidableEq

def keys (r : RawProgram) : List BlockId := r.blocks.map (·.1)

def RawBlock.rename (f : BlockId → BlockId) (b : RawBlock) : RawBlock :=
  { b with succs := b.succs.map f }

def applyRenaming (f : BlockId → BlockId) (r : RawProgram) : RawProgram :=
  { entry := f r.entry
    blocks := r.blocks.map (fun kv => (f kv.1, RawBlock.rename f kv.2)) }

structure IsRenaming (f g : BlockId → BlockId) : Prop where
  left : ∀ b, g (f b) = b
  right : ∀ b, f (g b) = b

theorem IsRenaming.injective {f g : BlockId → BlockId} (h : IsRenaming f g) :
    Function.Injective f := by
  intro a b hab
  have h' := congrArg g hab
  rwa [h.left, h.left] at h'

def AlphaEq (r s : RawProgram) : Prop :=
  ∃ f g, IsRenaming f g ∧ applyRenaming f r = s

def Renames (r s : RawProgram) : Prop :=
  ∃ f, Function.Injective f ∧ applyRenaming f r = s

theorem alphaEq_renames {r s : RawProgram} (h : AlphaEq r s) : Renames r s := by
  obtain ⟨f, g, hfg, heq⟩ := h
  exact ⟨f, hfg.injective, heq⟩

def idx (a : BlockId) : List BlockId → Nat
  | [] => 0
  | b :: t => if b = a then 0 else idx a t + 1

def canonId (r : RawProgram) : BlockId → BlockId := fun b => idx b (keys r)

def normalizeRaw (r : RawProgram) : RawProgram := applyRenaming (canonId r) r

structure ProgramWF (r : RawProgram) : Prop where
  keysNodup : (keys r).Nodup
  entryDeclared : r.entry ∈ keys r
  succsDeclared : ∀ kv ∈ r.blocks, ∀ b ∈ kv.2.succs, b ∈ keys r

/-! Re-derived infrastructure. -/

theorem keys_applyRenaming (f : BlockId → BlockId) (r : RawProgram) :
    keys (applyRenaming f r) = (keys r).map f := by
  simp [keys, applyRenaming, List.map_map, Function.comp_def]

theorem applyRenaming_comp (g f : BlockId → BlockId) (r : RawProgram) :
    applyRenaming g (applyRenaming f r) = applyRenaming (g ∘ f) r := by
  simp [applyRenaming, RawBlock.rename, List.map_map, Function.comp_def]

theorem applyRenaming_congr {f g : BlockId → BlockId} (h : f = g) (r : RawProgram) :
    applyRenaming f r = applyRenaming g r := by rw [h]

theorem applyRenaming_congr_on {f g : BlockId → BlockId} (r : RawProgram)
    (he : f r.entry = g r.entry)
    (hk : ∀ kv ∈ r.blocks, f kv.1 = g kv.1)
    (hs : ∀ kv ∈ r.blocks, ∀ b ∈ kv.2.succs, f b = g b) :
    applyRenaming f r = applyRenaming g r := by
  unfold applyRenaming
  simp only [RawProgram.mk.injEq]
  refine ⟨he, List.map_congr_left ?_⟩
  intro kv hkv
  simp only [Prod.mk.injEq]
  refine ⟨hk kv hkv, ?_⟩
  have hmg : kv.2.succs.map f = kv.2.succs.map g := List.map_congr_left (hs kv hkv)
  unfold RawBlock.rename
  rw [hmg]

theorem idx_map {f : BlockId → BlockId} (hf : Function.Injective f) (a : BlockId) :
    ∀ l : List BlockId, idx (f a) (l.map f) = idx a l
  | [] => rfl
  | b :: t => by
    rw [List.map_cons, idx, idx]
    by_cases h : b = a
    · subst h; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg h, if_neg (fun hc => h (hf hc)), idx_map hf a t]

theorem canonId_applyRenaming {f : BlockId → BlockId} (hf : Function.Injective f)
    (r : RawProgram) (b : BlockId) :
    canonId (applyRenaming f r) (f b) = canonId r b := by
  unfold canonId
  rw [keys_applyRenaming]
  exact idx_map hf b (keys r)

/-! ## §1 — control: the row itself re-derives, and is not vacuous

If the attacks below found nothing wrong with the row, that is because there is
nothing wrong with the row. It is re-proved here from scratch. -/

theorem normalizeRaw_rename_recheck {f : BlockId → BlockId} (hf : Function.Injective f)
    (r : RawProgram) :
    normalizeRaw (applyRenaming f r) = normalizeRaw r := by
  unfold normalizeRaw
  rw [applyRenaming_comp]
  exact applyRenaming_congr (funext fun b => canonId_applyRenaming hf r b) r

theorem normalizeRaw_alpha_recheck {r s : RawProgram} (h : AlphaEq r s) :
    normalizeRaw r = normalizeRaw s := by
  obtain ⟨f, hf, rfl⟩ := alphaEq_renames h
  exact (normalizeRaw_rename_recheck hf r).symm

/-! ## §2 — THE BREAK: `Renames` is not weaker than `AlphaEq`

The target states, twice, that quantifying the row over `Renames` (an
injection) rather than `AlphaEq` (a two-sided inverse) makes it "strictly
stronger": at `Renames`' docstring ("it is what makes the theorem below
strictly stronger than the scouted statement") and at `normalizeRaw_renames`
("Strictly stronger than the row: the premise is weaker").

It is not weaker. `applyRenaming f r` reads `f` at finitely many points — the
entry, the table keys, and the successor occurrences — and a finite partial
injection on `Nat` is completed to a permutation by finitely many
transpositions. So `Renames` and `AlphaEq` are the SAME relation, and no
normalizer whatsoever can tell the two rows apart.

Surjectivity is therefore not "used only to make `AlphaEq` symmetric" (target
divergence 2): at this carrier it is free. -/

/-- A transposition of the bound namespace. -/
def swp (x y b : BlockId) : BlockId := if b = x then y else if b = y then x else b

theorem swp_involutive (x y b : BlockId) : swp x y (swp x y b) = b := by
  unfold swp
  by_cases h1 : b = x
  · subst h1
    by_cases h2 : b = y
    · subst h2; simp
    · simp [Ne.symm h2]
  · by_cases h2 : b = y
    · subst h2; simp [h1]
    · simp [h1, h2]

/-- A bijection of the bound namespace, packaged with its inverse so that it can
be composed. This is `IsRenaming` carried as data; nothing new is minted. -/
structure Perm where
  to : BlockId → BlockId
  inv : BlockId → BlockId
  left : ∀ b, inv (to b) = b
  right : ∀ b, to (inv b) = b

theorem Perm.isRenaming (p : Perm) : IsRenaming p.to p.inv := ⟨p.left, p.right⟩

theorem Perm.injective (p : Perm) : Function.Injective p.to := p.isRenaming.injective

def Perm.idP : Perm := ⟨id, id, fun _ => rfl, fun _ => rfl⟩

def Perm.tr (x y : BlockId) : Perm :=
  ⟨swp x y, swp x y, swp_involutive x y, swp_involutive x y⟩

def Perm.after (q p : Perm) : Perm :=
  { to := fun b => q.to (p.to b)
    inv := fun b => p.inv (q.inv b)
    left := by intro b; rw [q.left, p.left]
    right := by intro b; rw [p.right, q.right] }

/-- **The completion lemma.** Any injection agrees with an honest bijection on
any finite list of points. Proof: process the points one at a time, correcting
the current bijection by one transposition; injectivity of `f` keeps the already
corrected points fixed. -/
theorem exists_perm_agreeing {f : BlockId → BlockId} (hf : Function.Injective f) :
    ∀ L : List BlockId, ∃ p : Perm, ∀ b ∈ L, p.to b = f b := by
  intro L
  induction L with
  | nil => exact ⟨Perm.idP, by intro b hb; cases hb⟩
  | cons a t ih =>
    obtain ⟨p, hp⟩ := ih
    by_cases hpa : p.to a = f a
    · refine ⟨p, ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact hpa
      · exact hp b hb'
    · refine ⟨(Perm.tr (p.to a) (f a)).after p, ?_⟩
      intro b hb
      have hfix : ∀ c : BlockId, c ∈ t → c ≠ a →
          ((Perm.tr (p.to a) (f a)).after p).to c = f c := by
        intro c hc hca
        show swp (p.to a) (f a) (p.to c) = f c
        have h1 : p.to c = f c := hp c hc
        have h2 : p.to c ≠ p.to a := fun hcc => hca (p.injective hcc)
        have h3 : p.to c ≠ f a := by rw [h1]; exact fun hcc => hca (hf hcc)
        unfold swp
        rw [if_neg h2, if_neg h3]
        exact h1
      have hat : ((Perm.tr (p.to a) (f a)).after p).to a = f a := by
        show swp (p.to a) (f a) (p.to a) = f a
        unfold swp
        rw [if_pos rfl]
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact hat
      · by_cases hba : b = a
        · subst hba; exact hat
        · exact hfix b hb' hba

/-- Every identifier occurrence of a block table, as a list. -/
def occBlocks : List (BlockId × RawBlock) → List BlockId
  | [] => []
  | kv :: t => kv.1 :: (kv.2.succs ++ occBlocks t)

/-- Every identifier occurrence of a program, as a list. -/
def occ (r : RawProgram) : List BlockId := r.entry :: occBlocks r.blocks

theorem mem_occBlocks_key : ∀ {bs : List (BlockId × RawBlock)} {kv : BlockId × RawBlock},
    kv ∈ bs → kv.1 ∈ occBlocks bs
  | [], _, h => absurd h (by simp)
  | c :: t, kv, h => by
    rcases List.mem_cons.mp h with rfl | h'
    · exact List.mem_cons.mpr (Or.inl rfl)
    · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr (mem_occBlocks_key h'))))

theorem mem_occBlocks_succ : ∀ {bs : List (BlockId × RawBlock)} {kv : BlockId × RawBlock}
    {b : BlockId}, kv ∈ bs → b ∈ kv.2.succs → b ∈ occBlocks bs
  | [], _, _, h, _ => absurd h (by simp)
  | c :: t, kv, b, h, hb => by
    rcases List.mem_cons.mp h with rfl | h'
    · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hb)))
    · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr (mem_occBlocks_succ h' hb))))

theorem mem_occ_entry (r : RawProgram) : r.entry ∈ occ r :=
  List.mem_cons.mpr (Or.inl rfl)

theorem mem_occ_key {r : RawProgram} {kv : BlockId × RawBlock} (h : kv ∈ r.blocks) :
    kv.1 ∈ occ r :=
  List.mem_cons.mpr (Or.inr (mem_occBlocks_key h))

theorem mem_occ_succ {r : RawProgram} {kv : BlockId × RawBlock} {b : BlockId}
    (h : kv ∈ r.blocks) (hb : b ∈ kv.2.succs) : b ∈ occ r :=
  List.mem_cons.mpr (Or.inr (mem_occBlocks_succ h hb))

/-- **The break.** An injective renaming is a bijective renaming, at this
carrier. -/
theorem renames_implies_alphaEq {r s : RawProgram} (h : Renames r s) : AlphaEq r s := by
  obtain ⟨f, hf, rfl⟩ := h
  obtain ⟨p, hp⟩ := exists_perm_agreeing hf (occ r)
  refine ⟨p.to, p.inv, p.isRenaming, ?_⟩
  exact applyRenaming_congr_on r (hp _ (mem_occ_entry r))
    (fun kv hkv => hp _ (mem_occ_key hkv))
    (fun kv hkv b hb => hp _ (mem_occ_succ hkv hb))

/-- The two premises the target treats as strictly ordered are one premise. -/
theorem renames_iff_alphaEq (r s : RawProgram) : Renames r s ↔ AlphaEq r s :=
  ⟨renames_implies_alphaEq, alphaEq_renames⟩

/-- So the target's claimed strengthening has no witness, and cannot acquire
one. -/
theorem no_pair_separates_renames_from_alphaEq :
    ¬ ∃ r s : RawProgram, Renames r s ∧ ¬ AlphaEq r s := by
  rintro ⟨r, s, hr, hn⟩
  exact hn (renames_implies_alphaEq hr)

/-- **The consequence for the DAG row.** For EVERY normalizer, the row over
`Renames` and the row over `AlphaEq` are the same statement.
`normalizeRaw_renames` is therefore not "strictly stronger than the row"; it is
the row, respelled. -/
theorem row_over_renames_iff_row_over_alphaEq (norm : RawProgram → RawProgram) :
    (∀ r s : RawProgram, Renames r s → norm r = norm s)
      ↔ (∀ r s : RawProgram, AlphaEq r s → norm r = norm s) := by
  constructor
  · intro h r s hrs; exact h r s (alphaEq_renames hrs)
  · intro h r s hrs; exact h r s (renames_implies_alphaEq hrs)

/-! ## §3 — THE SECOND BREAK: the normalizer reads an observable the declared
carrier does not have

`ALGEBRA.md:235` declares `blockTable   finite BlockId -> RawBlock map`. The
target models it as `List (BlockId × RawBlock)` — defensible, because
`ALGEBRA.md:240-243` also makes duplicate identifiers representable and a finite
map cannot hold them — and then builds `normalizeRaw` out of the ROW ORDER of
that list.

The two readings disagree exactly where it matters. Below, `two` and `twoPerm`
are duplicate-free, share an entry, and assign the same block to each key: the
same finite map, presented in two orders. `normalizeRaw` gives them different
normal forms, and puts different operations at the same canonical identifier.

Consequences the target does not record:

* under `ALGEBRA.md:235`'s reading `normalizeRaw` is not a function of the
  declared `blockTable` at all, so the row proved here is a statement about a
  presentation rather than about `EC1-D026`;
* under the assoc-list reading forced by `:240-243` it is a function, but it
  makes row order LOAD-BEARING, which is the opposite of `PROOF-DAG.md:100-102`'s
  declaration obligation "canonical ordering/normalization for rows and tables".
  The packet's shape for that obligation — `EC1-T002` (`PROOF-DAG.md:190`),
  `NodupKeys r -> NodupKeys s -> (rowEq r s <-> norm r = norm s)`, on the
  estate's `canonServices_perm_of_nodup_keys` — fails here at a DUPLICATE-FREE
  witness, which is precisely the case `EC1-CE030` leaves standing (`EC1-CE030`
  refutes only the premise-free form and its repair is a duplicate-free
  premise);
* `EC1-F82` is NOT what catches this. That falsifier is about duplicate-key
  rows, and the target survives it because it asserts no permutation law at
  all (`§5`);
* it is NOT forced by the target's §7. §7 rules out KEY-PRESERVING normalizers;
  it says nothing against a renumbering that is additionally row-permutation
  invariant, and §7's own argument goes through for such a normalizer
  unchanged;
* the target's §4 justification — "`EFFECTS-BACKEND` R4 — identity hashes
  PRESENTATIONS, not denotations — makes presentation order the estate's own
  canonical witness" — does not support the choice. R4 argues for a structural,
  decidable quotient BELOW semantic equivalence, names α-equivalence as the
  field's frontier, and cites Unison's name-erased AST hash as the exemplar
  (`EFFECTS-BACKEND.md:61-70`). It is neutral between presentation-order and
  reachability-order renumbering — both are structural and decidable — and its
  exemplar erases more presentation, not less. `ALGEBRA.md:237` also gives
  `presentation` its own field, which this model omits, so `blockTable` row
  order is not the thing R4 is talking about. -/

def blkA : RawBlock := { op := "a", succs := [] }
def blkB : RawBlock := { op := "b", succs := [] }

def two : RawProgram := { entry := 0, blocks := [(0, blkA), (1, blkB)] }
def twoPerm : RawProgram := { entry := 0, blocks := [(1, blkB), (0, blkA)] }

/-- Assoc lookup: the finite map a `blockTable` denotes. -/
def lookupB (r : RawProgram) (b : BlockId) : Option RawBlock :=
  (r.blocks.find? (fun kv => kv.1 == b)).map (·.2)

theorem twoPerm_is_a_row_permutation :
    twoPerm.entry = two.entry ∧ twoPerm.blocks = two.blocks.reverse := by decide

theorem two_nodup : (keys two).Nodup ∧ (keys twoPerm).Nodup := by decide

/-- Same entry, same finite map: at every identifier the two tables agree. -/
theorem twoPerm_same_finite_map (b : BlockId) : lookupB two b = lookupB twoPerm b := by
  by_cases h0 : b = 0
  · subst h0; rfl
  · by_cases h1 : b = 1
    · subst h1; rfl
    · simp [lookupB, two, twoPerm, Ne.symm h0, Ne.symm h1]

/-- **The break.** Equal finite maps, different normal forms. -/
theorem normalizeRaw_is_not_row_permutation_invariant :
    normalizeRaw two ≠ normalizeRaw twoPerm := by decide

/-- And the difference is not cosmetic: the two normal forms put different FREE
operation keys at the same canonical identifier, so no downstream consumer that
reads a block by its normalized identifier can be order-blind. -/
theorem row_order_moves_the_block_at_canonical_zero :
    lookupB (normalizeRaw two) 0 ≠ lookupB (normalizeRaw twoPerm) 0 := by decide

/-- Stated in the `EC1-T002` shape, so the gap is visible: the forward half of
the packet's row-normalization contract FAILS for this `normalizeRaw`, on
duplicate-free tables — precisely the case `EC1-CE030` leaves standing. -/
theorem nodup_row_permutation_law_fails_for_normalizeRaw :
    ¬ ∀ r s : RawProgram, (keys r).Nodup → (keys s).Nodup →
        r.entry = s.entry → r.blocks = s.blocks.reverse →
        normalizeRaw r = normalizeRaw s := by
  intro h
  exact normalizeRaw_is_not_row_permutation_invariant
    (h two twoPerm two_nodup.1 two_nodup.2 rfl (by decide))

/-! ## §4 — `ProgramWF` is not the premise §8's laws need

The target's §8 carries all three `ProgramWF` clauses into both
`normalizeRaw_renames_input` and `normalizeRaw_idempotent_of_wf`. Two of the
three are droppable at witnesses. Neither result is wrong; both are stated on a
smaller class than they hold on, which matters because `EC1-T006` is a separate
DAG row that the target discharges only under this premise. -/

theorem swp_injective (x y : BlockId) : Function.Injective (swp x y) := by
  intro a b hab
  have h := congrArg (swp x y) hab
  rwa [swp_involutive, swp_involutive] at h

/-- Duplicate keys: `keysNodup` fails. -/
def dupKeys : RawProgram := { entry := 1, blocks := [(1, blkA), (1, blkB)] }

theorem dupKeys_is_not_wf : ¬ (keys dupKeys).Nodup := by decide

/-- Soundness holds anyway. -/
theorem dupKeys_still_renames : Renames dupKeys (normalizeRaw dupKeys) :=
  ⟨swp 0 1, swp_injective 0 1, by decide⟩

/-- Undeclared entry: `entryDeclared` fails. -/
def entryFree : RawProgram := { entry := 5, blocks := [(0, blkA)] }

theorem entryFree_is_not_wf : entryFree.entry ∉ keys entryFree := by decide

theorem entryFree_still_renames : Renames entryFree (normalizeRaw entryFree) :=
  ⟨swp 5 1, swp_injective 5 1, by decide⟩

/-- `EC1-T006` (idempotence) at three programs none of which is `ProgramWF`:
duplicate keys, undeclared entry, dangling successors. The target proves
idempotence only under `ProgramWF`; the premise is not necessary at any of
them. (The general unconditional statement is NOT proved here — see the report's
omissions.) -/
def dangleL : RawProgram := { entry := 0, blocks := [(0, { op := "a", succs := [7, 8] })] }

theorem idempotence_without_wf :
    normalizeRaw (normalizeRaw dupKeys) = normalizeRaw dupKeys
      ∧ normalizeRaw (normalizeRaw entryFree) = normalizeRaw entryFree
      ∧ normalizeRaw (normalizeRaw dangleL) = normalizeRaw dangleL := by decide

/-! ## §5 — the F-battery on the row

`EC1-F01` (delete a target block) and `EC1-F03` (duplicate a block ID) are the
two falsifiers of the battery that reach this carrier. Both leave the row
standing. `EC1-F01` is caught by §8's soundness law and by nothing else, which
is evidence FOR the target's §8 diagnosis. -/

/-- `EC1-F03`: duplicate a block ID, then rename. The row holds. -/
theorem F03_row_survives_duplicate_keys :
    normalizeRaw (applyRenaming (swp 1 4) dupKeys) = normalizeRaw dupKeys := by decide

/-- `EC1-F01`: a program and the same program with its jump target deleted. -/
def linked : RawProgram :=
  { entry := 0, blocks := [(0, { op := "a", succs := [1] }), (1, blkB)] }
def deleted : RawProgram := { entry := 0, blocks := [(0, { op := "a", succs := [1] })] }

theorem linked_is_wf : ProgramWF linked :=
  { keysNodup := by decide
    entryDeclared := by decide
    succsDeclared := by decide }

theorem deleted_is_not_wf : ¬ ∀ kv ∈ deleted.blocks, ∀ b ∈ kv.2.succs, b ∈ keys deleted := by
  decide

/-- `EC1-F01` does not reach the row: the deleted program still satisfies it. -/
theorem F01_row_survives_deletion :
    normalizeRaw (applyRenaming (swp 0 9) deleted) = normalizeRaw deleted := by decide

theorem normalizeRaw_dangleL :
    normalizeRaw dangleL = { entry := 0, blocks := [(0, { op := "a", succs := [1, 1] })] } := by
  decide

/-- `EC1-F01`/dangling references ARE caught by §8's soundness law, and the
`succsDeclared` clause is therefore necessary there — the one `ProgramWF` clause
§4 above could not drop. -/
theorem dangle_not_renames : ¬ Renames dangleL (normalizeRaw dangleL) := by
  rintro ⟨f, hf, heq⟩
  rw [normalizeRaw_dangleL] at heq
  simp only [applyRenaming, dangleL, RawBlock.rename, List.map_cons, List.map_nil,
    RawProgram.mk.injEq, List.cons.injEq, Prod.mk.injEq, RawBlock.mk.injEq,
    and_true, true_and] at heq
  obtain ⟨-, -, h7, h8⟩ := heq
  exact absurd (hf (h7.trans h8.symm)) (by decide)

/-! ## §6 — `free_namespace_refutes_the_row` does not refute THIS row

The target's theorem is `normalizeRaw (renameOps swapOp two) ≠ normalizeRaw
two`. That is true, and it is the right warning about an undeclared bound/free
split in the packet. But it is NOT a refutation of the row the file declares:
`renameOps swapOp two` is not `AlphaEq` to `two`, so the row never claimed
anything about it. The name overstates the scope. -/

def renameOps (σ : OpId → OpId) (r : RawProgram) : RawProgram :=
  { r with blocks := r.blocks.map (fun kv => (kv.1, { kv.2 with op := σ kv.2.op })) }

def swapOp : OpId → OpId := fun s => if s = "a" then "b" else if s = "b" then "a" else s

theorem opSwap_is_not_alphaEq : ¬ AlphaEq two (renameOps swapOp two) := by
  rintro ⟨f, g, hfg, heq⟩
  have h := congrArg (fun p => p.blocks.map (fun kv => kv.2.op)) heq
  simp only [applyRenaming, renameOps, two, blkA, blkB, swapOp, RawBlock.rename,
    List.map_cons, List.map_nil] at h
  exact absurd h (by decide)

/-- Consequently the file's own row is untouched by the op swap: the pair is
outside its hypothesis, so no instance of `normalizeRaw_alpha` is contradicted.
The theorem constrains a HYPOTHETICAL alphaEq that ranges over the free
namespace — which is the packet's gap, not this row's. -/
theorem free_namespace_theorem_is_out_of_the_rows_scope :
    ¬ AlphaEq two (renameOps swapOp two)
      ∧ (∀ r s : RawProgram, AlphaEq r s → normalizeRaw r = normalizeRaw s) :=
  ⟨opSwap_is_not_alphaEq, fun _ _ h => normalizeRaw_alpha_recheck h⟩

/-! ## §7 — the headline obstruction survives strengthening

The one repair a reader would reach for is to restrict `hpres` to well-formed
programs — "of course a normalizer preserves keys only on programs it accepts".
It does not help: shifting a well-formed program leaves it well-formed, so the
obstruction still fires. This is a falsifier the target's §7 SURVIVES. -/

def maxKey (r : RawProgram) : Nat := (keys r).foldr max 0

theorem le_foldr_max {l : List Nat} {b : Nat} (h : b ∈ l) : b ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons c t ih =>
    rcases List.mem_cons.mp h with h1 | h2
    · subst h1; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h2) (Nat.le_max_right _ _)

theorem shift_injective (n : Nat) : Function.Injective (fun b : BlockId => b + n) := by
  intro a b h
  exact Nat.add_right_cancel h

/-- Stated at `Nat`: `omega` does not see through the `BlockId` abbreviation.
(Confirmed independently here — the target's §7 note is correct.) -/
theorem shift_absurd {k n b : Nat} (hk : k + (n + 1) = b) (hle : b ≤ n) : False := by omega

theorem wf_applyRenaming {f : BlockId → BlockId} (hf : Function.Injective f)
    {r : RawProgram} (h : ProgramWF r) : ProgramWF (applyRenaming f r) := by
  refine { keysNodup := ?_, entryDeclared := ?_, succsDeclared := ?_ }
  · rw [keys_applyRenaming]
    exact List.Pairwise.map f (fun a b hab hc => hab (hf hc)) h.keysNodup
  · rw [keys_applyRenaming]
    exact List.mem_map.mpr ⟨r.entry, h.entryDeclared, rfl⟩
  · intro kv hkv b hb
    rw [keys_applyRenaming]
    obtain ⟨kv0, hkv0, rfl⟩ := List.mem_map.mp hkv
    simp only [RawBlock.rename] at hb
    obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
    exact List.mem_map.mpr ⟨b0, h.succsDeclared kv0 hkv0 b0 hb0, rfl⟩

/-- **The obstruction, with `hpres` restricted to well-formed programs.** Still
forces an empty result, so no well-formedness premise rescues a key-preserving
renaming-stable normalizer. -/
theorem preserve_keys_obstruction_survives_wf_restriction
    (norm : RawProgram → RawProgram)
    (hrow : ∀ f : BlockId → BlockId, Function.Injective f →
        ∀ r, norm (applyRenaming f r) = norm r)
    (hpres : ∀ r, ProgramWF r → ∀ b ∈ keys (norm r), b ∈ keys r)
    {r : RawProgram} (hwf : ProgramWF r) : keys (norm r) = [] := by
  cases hcase : keys (norm r) with
  | nil => rfl
  | cons b t =>
    exfalso
    have hb : b ∈ keys (norm r) := by rw [hcase]; exact List.Mem.head t
    have hle : b ≤ maxKey r := le_foldr_max (hpres r hwf b hb)
    have hshift := shift_injective (maxKey r + 1)
    have hb2 : b ∈ keys (norm (applyRenaming (fun x => x + (maxKey r + 1)) r)) := by
      rw [hrow _ hshift r]; exact hb
    have hmem := hpres _ (wf_applyRenaming hshift hwf) b hb2
    rw [keys_applyRenaming] at hmem
    obtain ⟨k, _, hk⟩ := List.mem_map.mp hmem
    have hk' : k + (maxKey r + 1) = b := hk
    exact shift_absurd hk' hle

/-- And the well-formed instance is inhabited, so the strengthened obstruction
is not vacuous: `linked` is well-formed and its normal form has keys. -/
theorem wf_obstruction_is_not_vacuous :
    ProgramWF linked ∧ keys (normalizeRaw linked) ≠ [] :=
  ⟨linked_is_wf, by decide⟩

/-! ## §8 — the modelled normal form is not the estate's normal form

`EC1-CE040` (`VERIFIED-KERNEL`) records that the estate's `toPProg` "is only a
sound recognizer for one literal normal form", refuted by `entryNotZero` and
`unreachableTail`. This model's `normalizeRaw` produces neither: it leaves the
entry wherever presentation order puts it, and it keeps unreachable blocks.
Both facts are compatible with everything the target proves — they bound the
claim, they do not break it. -/

def entryLast : RawProgram := { entry := 1, blocks := [(0, blkA), (1, blkB)] }

theorem entryLast_is_wf : ProgramWF entryLast :=
  { keysNodup := by decide
    entryDeclared := by decide
    succsDeclared := by decide }

/-- Even on a well-formed program the normal form does not put the entry at
block `0`, so it is not `EC1-CE040`'s literal normal form. -/
theorem normalizeRaw_does_not_normalize_the_entry :
    (normalizeRaw entryLast).entry ≠ 0 := by decide

/-- And unreachable blocks are retained, so it is not a reachability
normalization either. `two`'s block `1` is unreachable from its entry. -/
theorem normalizeRaw_retains_unreachable_blocks :
    (normalizeRaw two).blocks.length = 2 := by decide

/-! ## §9 — one packet-level fact, recorded without a theorem

`PROOF-DAG.md:499` gives slice `EC1-S1` the declarations **D0–D1** and the exit
`T001–T009`; `:500` gives `EC1-S2` the declarations **D2–D3** and the exit
`T006–T017`. `EC1-T007` is about `EC1-D020 RawProgram` and `EC1-D026
normalizeRaw` (`PROOF-DAG.md:107`, `:114`), both **D2** terms. So this row is
dispatched in a slice whose declaration budget does not contain the terms it
quantifies over, and it also appears in `EC1-S2`'s exit list. The target's
carrier invention is therefore forced by the ledger, not chosen; and a green
`EC1-T007` proved under `EC1-S1` cannot close the `EC1-S2` row it is also
listed in. `EC1-F80` (cutover with an open required-type edge) is the falsifier
that should catch a cutover claimed on this basis.

## §10 — receipts

Every theorem above carries `#print axioms`. The ceiling is `[propext,
Quot.sound]`; no `Classical.choice`, no `sorryAx`. No `sorry`, no `axiom`, no
`native_decide`, no `#eval` carrying a claim.

For the record, the target file prints 47 receipts for 51 declared theorems:
`normalizeRaw_def`, `shift_absurd`, `lt_self_absurd` and `add_cancel_succ` have
no `#print axioms` line, contradicting its §11 claim of "`#print axioms` on every
theorem". All four are used, so their axiom dependencies do reach the printed
receipts transitively; the gap is bookkeeping, not trust. -/

#print axioms EffectCoreV1.AttackT007.IsRenaming.injective
#print axioms EffectCoreV1.AttackT007.alphaEq_renames
#print axioms EffectCoreV1.AttackT007.keys_applyRenaming
#print axioms EffectCoreV1.AttackT007.applyRenaming_comp
#print axioms EffectCoreV1.AttackT007.applyRenaming_congr
#print axioms EffectCoreV1.AttackT007.applyRenaming_congr_on
#print axioms EffectCoreV1.AttackT007.idx_map
#print axioms EffectCoreV1.AttackT007.canonId_applyRenaming
#print axioms EffectCoreV1.AttackT007.normalizeRaw_rename_recheck
#print axioms EffectCoreV1.AttackT007.normalizeRaw_alpha_recheck
#print axioms EffectCoreV1.AttackT007.swp_involutive
#print axioms EffectCoreV1.AttackT007.Perm.isRenaming
#print axioms EffectCoreV1.AttackT007.Perm.injective
#print axioms EffectCoreV1.AttackT007.exists_perm_agreeing
#print axioms EffectCoreV1.AttackT007.mem_occBlocks_key
#print axioms EffectCoreV1.AttackT007.mem_occBlocks_succ
#print axioms EffectCoreV1.AttackT007.mem_occ_entry
#print axioms EffectCoreV1.AttackT007.mem_occ_key
#print axioms EffectCoreV1.AttackT007.mem_occ_succ
#print axioms EffectCoreV1.AttackT007.renames_implies_alphaEq
#print axioms EffectCoreV1.AttackT007.renames_iff_alphaEq
#print axioms EffectCoreV1.AttackT007.no_pair_separates_renames_from_alphaEq
#print axioms EffectCoreV1.AttackT007.row_over_renames_iff_row_over_alphaEq
#print axioms EffectCoreV1.AttackT007.twoPerm_is_a_row_permutation
#print axioms EffectCoreV1.AttackT007.two_nodup
#print axioms EffectCoreV1.AttackT007.twoPerm_same_finite_map
#print axioms EffectCoreV1.AttackT007.normalizeRaw_is_not_row_permutation_invariant
#print axioms EffectCoreV1.AttackT007.row_order_moves_the_block_at_canonical_zero
#print axioms EffectCoreV1.AttackT007.nodup_row_permutation_law_fails_for_normalizeRaw
#print axioms EffectCoreV1.AttackT007.swp_injective
#print axioms EffectCoreV1.AttackT007.dupKeys_is_not_wf
#print axioms EffectCoreV1.AttackT007.dupKeys_still_renames
#print axioms EffectCoreV1.AttackT007.entryFree_is_not_wf
#print axioms EffectCoreV1.AttackT007.entryFree_still_renames
#print axioms EffectCoreV1.AttackT007.idempotence_without_wf
#print axioms EffectCoreV1.AttackT007.F03_row_survives_duplicate_keys
#print axioms EffectCoreV1.AttackT007.linked_is_wf
#print axioms EffectCoreV1.AttackT007.deleted_is_not_wf
#print axioms EffectCoreV1.AttackT007.F01_row_survives_deletion
#print axioms EffectCoreV1.AttackT007.normalizeRaw_dangleL
#print axioms EffectCoreV1.AttackT007.dangle_not_renames
#print axioms EffectCoreV1.AttackT007.opSwap_is_not_alphaEq
#print axioms EffectCoreV1.AttackT007.free_namespace_theorem_is_out_of_the_rows_scope
#print axioms EffectCoreV1.AttackT007.le_foldr_max
#print axioms EffectCoreV1.AttackT007.shift_injective
#print axioms EffectCoreV1.AttackT007.shift_absurd
#print axioms EffectCoreV1.AttackT007.wf_applyRenaming
#print axioms EffectCoreV1.AttackT007.preserve_keys_obstruction_survives_wf_restriction
#print axioms EffectCoreV1.AttackT007.wf_obstruction_is_not_vacuous
#print axioms EffectCoreV1.AttackT007.entryLast_is_wf
#print axioms EffectCoreV1.AttackT007.normalizeRaw_does_not_normalize_the_entry
#print axioms EffectCoreV1.AttackT007.normalizeRaw_retains_unreachable_blocks

end EffectCoreV1.AttackT007
