import Cas.Core.Canonicalize

/-!
# `EC1-T007` — `normalizeRaw_alpha`

Slice `EC1-S1`. Skill stage: **`lean-model-invariants`** (the row is about the
representation of a raw carrier and its canonical form — the stage's
`Canonical form + normalizer` representation row and its named obligations
"normalization soundness and idempotence" are the ones applied below).

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/T007.lean
```

This file is OUTSIDE every lake target. It modifies nothing under `library/`
and nothing under `formal/effect-core-v1/`. Its intended home,
`formal/effect-core-v1/EffectCore/Syntax/Raw.lean`, is a reserved stub and is
deliberately not written to; a later integration step moves proofs into
modules.

## The DAG row

```text
EC1-T007 | normalizeRaw_alpha : alphaEq r s -> normalizeRaw r = normalizeRaw s | D2, T006
```
(`PROOF-DAG.md:199`, verified.)

`alphaEq` is not a declared term anywhere in the packet or the estate;
`RawProgram` (`EC1-D020`) and `normalizeRaw` (`EC1-D026`) do not exist in Lean.
So the row has no truth value as written and this file must supply a carrier
before it can say anything. It supplies a MINIMAL, first-order one — the
smallest model that keeps every feature the row's difficulty depends on:

* a BOUND identifier namespace (`BlockId`) that occurs both as a table KEY and
  as an OCCURRENCE inside a block, so a renaming has something to capture;
* a FREE namespace (`RawBlock.op`) — a key into host code, `EFFECTS-BACKEND` R7
  — that a renaming may NOT move;
* deliberate invalid states: duplicate keys and dangling references are
  representable, exactly as `ALGEBRA.md:240-243` requires of `EC1-A11`.

## What is proved here

| § | Statement | Result |
|---|---|---|
| 2 | `AlphaEq` is an equivalence relation, defined WITHOUT `normalizeRaw` | proved |
| 3 | the normal-form reading of `alphaEq` makes the row `Iff.rfl` | proved (the trap) |
| 5 | `normalizeRaw_rename` — renaming stability, INJECTIVE renamings only | proved |
| 5 | **`normalizeRaw_alpha` — THE ROW** | **proved** |
| 5 | the row is EQUIVALENT to renaming stability | proved |
| 6 | injectivity is load-bearing: a collapsing renaming refutes the row | proved |
| 6 | the BOUND/FREE split is load-bearing: renaming `op` refutes the row | proved |
| 6 | `EC1-T006` (idempotence) does not imply the row | proved |
| 7 | **PRESERVE-keys is INCOMPATIBLE with the row** | proved (new obstruction) |
| 7 | consequently `normalizeRaw` cannot be key-preserving | proved |
| 8 | `normalizeRaw` is a renaming of its input on well-formed programs | proved |
| 8 | the discarding normalizer satisfies the row and fails that | proved |
| 8 | idempotence (`EC1-T006`) as a COROLLARY, on well-formed programs | proved |
| 9 | the row is not vacuous, and its conclusion is not universally true | proved |
| 9 | **the scouted COMPLETENESS half is FALSE premise-free** | proved (refutation) |
| 9 | `AlphaEq` is NOT normal-form equality here | proved (escapes §3's trap) |

## Divergence from the DAG signature — read this before citing the row

Every departure is recorded in one place, `§10`. The four that matter:

1. `alphaEq` is promoted to a DECLARED relation `AlphaEq`, defined by a
   bijective renaming action and NOT through `normalizeRaw`. §3 proves the
   alternative spelling is `Iff.rfl`.
2. The scout asked for `Renaming.Bijective`. `Function.Bijective` does not
   exist in this toolchain (verified: `#check @Function.Bijective` fails;
   `library/cas` pins `leanprover/lean4:v4.33.1` with no Mathlib), so
   bijectivity is spelled as a two-sided inverse. More importantly the ROW
   needs only INJECTIVITY — surjectivity is used solely to make `AlphaEq`
   symmetric. The load-bearing lemma is therefore stated over `Renames`
   (injective renamings), which is strictly stronger.
3. The scout's `ProgramWF r` premise is DROPPED. It is not needed, and §7
   explains why the `EC1-CE030` transfer he flagged "by shape, not proved"
   does NOT fire here: a last-wins-plus-key-sort normalizer, the shape CE030
   attacks, cannot satisfy this row AT ALL (§7), so no premise rescues it.
   A presentation-order renumbering needs no duplicate-free premise.
4. `normalizeRaw` is a CONCRETE presentation-order renumbering, not the
   packet's declared term. Everything below is therefore about this model,
   not assurance about `EC1-D026`.
-/

namespace EffectCoreV1.T007

/-! ## §1 — the carrier

`EC1-A11`'s eight tables are collapsed to one (`blockTable`) plus `entry`.
That is the smallest shape in which a renaming both re-keys a table and
rewrites occurrences. `op` stands for the FREE namespaces the real carrier
carries alongside — `alphabetVersion`, the `publicSurface` ledger identity,
operation IDs, `foreignTable` registry keys. `EFFECTS-BACKEND` R7 makes those
keys into host code; §6 proves the row is FALSE if a renaming is allowed to
move them. -/

/-- A BOUND identifier. `ALGEBRA.md:240`: "Raw identifiers are ordinary bounded
numbers or canonical names." -/
abbrev BlockId := Nat

/-- A FREE identifier: a key into host code (R7). Renamings never touch it. -/
abbrev OpId := String

/-- One raw block: a free operation key and its bound successors. -/
structure RawBlock where
  op : OpId
  succs : List BlockId
  deriving DecidableEq

/-- The raw carrier. Duplicate keys and dangling successors are representable,
per `ALGEBRA.md:240-243`. -/
structure RawProgram where
  entry : BlockId
  blocks : List (BlockId × RawBlock)
  deriving DecidableEq

/-- The declared block identifiers, in presentation order. -/
def keys (r : RawProgram) : List BlockId := r.blocks.map (·.1)

/-! ## §2 — renaming and `AlphaEq`

`AlphaEq` is defined by a group action, INDEPENDENTLY of any normalizer. §3
shows why that independence is the whole of the row's content.

`Function.Bijective` does not exist in this toolchain, so a bijection is
spelled as a two-sided inverse. That is also the constructive spelling a
capture-avoiding renaming actually needs. -/

/-- Renaming inside a block. Only `succs` moves; `op` is FREE (R7). -/
def RawBlock.rename (f : BlockId → BlockId) (b : RawBlock) : RawBlock :=
  { b with succs := b.succs.map f }

/-- The renaming action on the whole program: entry, every table key, and
every occurrence. Capture-avoidance is automatic here because a renaming is a
FUNCTION applied uniformly — the estate's `PIn` (`Cas/Lang/Defun.lean:167`) is
positional for the same reason. -/
def applyRenaming (f : BlockId → BlockId) (r : RawProgram) : RawProgram :=
  { entry := f r.entry
    blocks := r.blocks.map (fun kv => (f kv.1, RawBlock.rename f kv.2)) }

/-- A bijection of the bound namespace, spelled as a two-sided inverse. -/
structure IsRenaming (f g : BlockId → BlockId) : Prop where
  left : ∀ b, g (f b) = b
  right : ∀ b, f (g b) = b

theorem IsRenaming.injective {f g : BlockId → BlockId} (h : IsRenaming f g) :
    Function.Injective f := by
  intro a b hab
  have h' := congrArg g hab
  rwa [h.left, h.left] at h'

/-- **`alphaEq`, declared.** Two raw programs are alpha-equivalent when one is
the other with its BOUND namespace bijectively renamed. Nothing here mentions
`normalizeRaw`. -/
def AlphaEq (r s : RawProgram) : Prop :=
  ∃ f g, IsRenaming f g ∧ applyRenaming f r = s

/-- The weaker relation the row's PROOF actually uses: renaming by an
injection. `AlphaEq` implies it (`alphaEq_renames`), and it is what makes the
theorem below strictly stronger than the scouted statement. -/
def Renames (r s : RawProgram) : Prop :=
  ∃ f, Function.Injective f ∧ applyRenaming f r = s

theorem applyRenaming_id (r : RawProgram) : applyRenaming id r = r := by
  cases r with
  | mk entry blocks =>
    simp [applyRenaming, RawBlock.rename]

theorem applyRenaming_comp (g f : BlockId → BlockId) (r : RawProgram) :
    applyRenaming g (applyRenaming f r) = applyRenaming (g ∘ f) r := by
  simp [applyRenaming, RawBlock.rename, List.map_map, Function.comp_def]

theorem applyRenaming_congr {f g : BlockId → BlockId} (h : f = g) (r : RawProgram) :
    applyRenaming f r = applyRenaming g r := by rw [h]

theorem keys_applyRenaming (f : BlockId → BlockId) (r : RawProgram) :
    keys (applyRenaming f r) = (keys r).map f := by
  simp [keys, applyRenaming, List.map_map, Function.comp_def]

theorem alphaEq_renames {r s : RawProgram} (h : AlphaEq r s) : Renames r s := by
  obtain ⟨f, g, hfg, heq⟩ := h
  exact ⟨f, hfg.injective, heq⟩

/-! `AlphaEq` is an equivalence relation. This is what the two-sided inverse
buys; the row itself does not need it. -/

theorem AlphaEq.refl (r : RawProgram) : AlphaEq r r :=
  ⟨id, id, ⟨fun _ => rfl, fun _ => rfl⟩, applyRenaming_id r⟩

theorem AlphaEq.symm {r s : RawProgram} (h : AlphaEq r s) : AlphaEq s r := by
  obtain ⟨f, g, hfg, rfl⟩ := h
  refine ⟨g, f, ⟨hfg.right, hfg.left⟩, ?_⟩
  rw [applyRenaming_comp]
  have : g ∘ f = id := funext hfg.left
  rw [this, applyRenaming_id]

theorem AlphaEq.trans {r s t : RawProgram} (h₁ : AlphaEq r s) (h₂ : AlphaEq s t) :
    AlphaEq r t := by
  obtain ⟨f₁, g₁, h₁', rfl⟩ := h₁
  obtain ⟨f₂, g₂, h₂', rfl⟩ := h₂
  refine ⟨f₂ ∘ f₁, g₁ ∘ g₂, ⟨?_, ?_⟩, (applyRenaming_comp f₂ f₁ r).symm⟩
  · intro b; simp only [Function.comp_apply]; rw [h₂'.left, h₁'.left]
  · intro b; simp only [Function.comp_apply]; rw [h₁'.right, h₂'.right]

/-! ## §3 — the tautology trap, and the escape

The estate already owns a canonicalizer whose induced equivalence is DEFINED
as equality of normal forms: `Cas.Canonicalizer.Equiv c a b := c.canon a =
c.canon b` (`Cas/Core/Canonicalize.lean:81`, read and verified). If the packet
spells `alphaEq` that way — and the row's stated dependency on `EC1-T006` is
evidence a normal-form route is intended — the row's proof term is its own
hypothesis. `PROOF-DAG.md:203-206` already deleted two rows of exactly this
defect class. -/

/-- **The trap, at the ESTATE's own object.** Reuse, not a local re-spelling:
this is `Cas.Canonicalizer.Equiv` verbatim. -/
theorem canon_equiv_reading_is_iff_rfl
    (c : Cas.Canonicalizer RawProgram) (r s : RawProgram) :
    c.Equiv r s ↔ c.canon r = c.canon s := Iff.rfl

/-- And in the row's own shape: read that way the row holds of EVERY function
whatsoever, `normalizeRaw` included, with no proof. -/
theorem normal_form_reading_makes_the_row_free
    (norm : RawProgram → RawProgram) (r s : RawProgram) (h : norm r = norm s) :
    norm r = norm s := h

/-! ## §4 — the normalizer

`normalizeRaw` renumbers every bound occurrence by the position of its block in
the PRESENTATION order of the table. That choice is forced twice over:

* §7 proves no key-order-preserving normalizer can satisfy the row at all, so
  the sort-by-identifier reflex (`canonServices`, `Cas/Backend/EmitLayer.lean:220`)
  is unavailable here — a renaming permutes the key space and sorting is by key
  order, which is precisely the scout's `swapKey` refutation;
* `EFFECTS-BACKEND` R4 — identity hashes PRESENTATIONS, not denotations — makes
  presentation order the estate's own canonical witness.

`idx` is a local list helper, not a minted packet term. `List.idxOf` would do
the same job, but its `BEq`/`LawfulBEq` route drags `Classical.choice` into
every receipt below for no mathematical reason; `idx` keeps the ceiling at
`propext`. -/

/-- First position of `a` in `l`, or `l.length` when absent. -/
def idx (a : BlockId) : List BlockId → Nat
  | [] => 0
  | b :: t => if b = a then 0 else idx a t + 1

/-- **The equivariance lemma.** Position is blind to an INJECTIVE relabelling
of the whole list. Injectivity is exactly what makes the "already seen?" test
agree on both sides; §6 shows dropping it refutes the row. -/
theorem idx_map {f : BlockId → BlockId} (hf : Function.Injective f) (a : BlockId) :
    ∀ l : List BlockId, idx (f a) (l.map f) = idx a l
  | [] => rfl
  | b :: t => by
    rw [List.map_cons, idx, idx]
    by_cases h : b = a
    · subst h; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg h, if_neg (fun hc => h (hf hc)), idx_map hf a t]

/-- The canonical identifier of a block: its presentation position. Every
identifier the table does not declare is sent to ONE slot, `(keys r).length`.
That collapse is not sloppiness — §7's argument shows a normalizer cannot both
be renaming-stable and keep undeclared identifiers apart. -/
def canonId (r : RawProgram) : BlockId → BlockId := fun b => idx b (keys r)

/-- **`EC1-D026`, modelled.** Renumber every bound occurrence by presentation
position. Note it is literally a renaming action applied to the program — that
identity is what makes §8 cheap. -/
def normalizeRaw (r : RawProgram) : RawProgram := applyRenaming (canonId r) r

theorem normalizeRaw_def (r : RawProgram) :
    normalizeRaw r = applyRenaming (canonId r) r := rfl

/-! ## §5 — the row -/

theorem canonId_applyRenaming {f : BlockId → BlockId} (hf : Function.Injective f)
    (r : RawProgram) (b : BlockId) :
    canonId (applyRenaming f r) (f b) = canonId r b := by
  unfold canonId
  rw [keys_applyRenaming]
  exact idx_map hf b (keys r)

/-- **The load-bearing lemma the DAG has no row for.** `normalizeRaw` is
constant on renaming orbits. The scout proved (`ScoutT007.alpha_row_iff_
renaming_stable`) that this is EQUIVALENT to the row; `row_iff_renaming_stable`
below re-proves that at this carrier. `EC1-T006` does not reach it (§6). -/
theorem normalizeRaw_rename {f : BlockId → BlockId} (hf : Function.Injective f)
    (r : RawProgram) :
    normalizeRaw (applyRenaming f r) = normalizeRaw r := by
  unfold normalizeRaw
  rw [applyRenaming_comp]
  exact applyRenaming_congr (funext fun b => canonId_applyRenaming hf r b) r

/-- **`EC1-T007`, over injective renamings.** Strictly stronger than the row:
the premise is weaker (`Renames`, not `AlphaEq`). -/
theorem normalizeRaw_renames {r s : RawProgram} (h : Renames r s) :
    normalizeRaw r = normalizeRaw s := by
  obtain ⟨f, hf, rfl⟩ := h
  exact (normalizeRaw_rename hf r).symm

/-- **`EC1-T007`. THE ROW.**

`normalizeRaw_alpha : AlphaEq r s -> normalizeRaw r = normalizeRaw s`.

No `ProgramWF` premise; see `§10` divergence 3. -/
theorem normalizeRaw_alpha {r s : RawProgram} (h : AlphaEq r s) :
    normalizeRaw r = normalizeRaw s :=
  normalizeRaw_renames (alphaEq_renames h)

/-- The row and renaming stability are the same statement, at this carrier and
over any renaming action. This is the scout's §3 re-proved locally, and it is
why `EC1-T006` cannot be the row's real dependency. -/
theorem row_iff_renaming_stable
    (norm : RawProgram → RawProgram) (act : (BlockId → BlockId) → RawProgram → RawProgram)
    (S : (BlockId → BlockId) → Prop) :
    (∀ r s : RawProgram, (∃ f, S f ∧ act f r = s) → norm r = norm s)
      ↔ (∀ f, S f → ∀ r, norm (act f r) = norm r) := by
  constructor
  · intro h f hf r
    exact (h r (act f r) ⟨f, hf, rfl⟩).symm
  · intro h r s hrs
    obtain ⟨f, hf, rfl⟩ := hrs
    exact (h f hf r).symm

/-! ## §6 — the premises that are load-bearing, and the one dependency that is not

Three witnesses. Each is a concrete refutation, not an argument. -/

def blkA : RawBlock := { op := "a", succs := [] }
def blkB : RawBlock := { op := "b", succs := [] }

/-- Two declared blocks, entry at the first. -/
def two : RawProgram := { entry := 0, blocks := [(0, blkA), (1, blkB)] }

/-- A COLLAPSING relabelling: not a renaming, because it is not injective. -/
def collapse : BlockId → BlockId := fun _ => 0

/-- **Injectivity is load-bearing.** Drop it from `normalizeRaw_rename` — i.e.
admit a non-injective relabelling into `AlphaEq` — and the row is false, for
row-identity reasons alone: two declared blocks are merged onto one key. -/
theorem injectivity_is_necessary :
    normalizeRaw (applyRenaming collapse two) ≠ normalizeRaw two := by decide

/-- Stated in the row's own shape, so the premise is visibly the one at issue. -/
theorem row_is_false_without_injectivity :
    ¬ ∀ (f : BlockId → BlockId) (r : RawProgram),
        normalizeRaw (applyRenaming f r) = normalizeRaw r :=
  fun h => injectivity_is_necessary (h collapse two)

/-- Renaming the FREE namespace. `EFFECTS-BACKEND` R7 — programs are content,
hosts are code — makes `op` a key into host code, so this is not a renaming of
the program at all; it is a rewrite of what the program CALLS. -/
def renameOps (σ : OpId → OpId) (r : RawProgram) : RawProgram :=
  { r with blocks := r.blocks.map (fun kv => (kv.1, { kv.2 with op := σ kv.2.op })) }

/-- The transposition of two operation keys. A bijection, by
`swapOp_involutive` — so no strengthening of `alphaEq`'s bijectivity clause
excludes it. Only a declared BOUND/FREE split does. -/
def swapOp : OpId → OpId := fun s => if s = "a" then "b" else if s = "b" then "a" else s

theorem swapOp_involutive (s : OpId) : swapOp (swapOp s) = s := by
  unfold swapOp
  by_cases h1 : s = "a"
  · subst h1; rfl
  · by_cases h2 : s = "b"
    · subst h2; rfl
    · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]

theorem swapOp_injective : Function.Injective swapOp := by
  intro x y h
  have hx := swapOp_involutive x
  rw [h, swapOp_involutive y] at hx
  exact hx.symm

/-- **The BOUND/FREE split is load-bearing.** `ALGEBRA.md:227-237` gives
`RawProgram` eleven fields whose identifiers mix internal `BlockId`/`CodeId`/
`RegionId` with `alphabetVersion`, the `publicSurface` ledger identity,
operation IDs and `foreignTable` registry keys. The packet nowhere declares
which namespaces are bound. Until it does, `alphaEq` quantifies over
relabellings that change meaning, and this is one: a bijection of the FREE
namespace refutes the row. This is the scout's §4 scope caveat, proved at a
carrier that actually has both namespaces. -/
theorem free_namespace_refutes_the_row :
    normalizeRaw (renameOps swapOp two) ≠ normalizeRaw two := by decide

/-- The transposition of two block identifiers: a genuine renaming. -/
def swapId (x y : BlockId) : BlockId → BlockId :=
  fun b => if b = x then y else if b = y then x else b

theorem swapId_involutive (x y b : BlockId) : swapId x y (swapId x y b) = b := by
  unfold swapId
  by_cases h1 : b = x
  · subst h1
    by_cases h2 : b = y
    · subst h2; simp
    · simp [Ne.symm h2]
  · by_cases h2 : b = y
    · subst h2; simp [h1]
    · simp [h1, h2]

theorem swapId_isRenaming (x y : BlockId) : IsRenaming (swapId x y) (swapId x y) :=
  ⟨swapId_involutive x y, swapId_involutive x y⟩

theorem swapId_injective (x y : BlockId) : Function.Injective (swapId x y) :=
  (swapId_isRenaming x y).injective

/-- **`EC1-T006` does not imply `EC1-T007`.** The row's stated dependency on
idempotence buys nothing: the identity normalizer is idempotent and is refuted
by a bijective renaming. The scout proved the same at the estate's shipped
`canonServices`; this is the statement at the packet's own carrier shape. -/
theorem T006_does_not_imply_T007 :
    ∃ norm : RawProgram → RawProgram,
      (∀ r, norm (norm r) = norm r) ∧
      ¬ (∀ f : BlockId → BlockId, Function.Injective f →
          ∀ r, norm (applyRenaming f r) = norm r) := by
  refine ⟨id, fun _ => rfl, fun h => ?_⟩
  have hbad : applyRenaming (swapId 0 1) two = two := h (swapId 0 1) (swapId_injective 0 1) two
  exact absurd hbad (by decide)

/-! ## §7 — a new obstruction: PRESERVE-keys is INCOMPATIBLE with the row

The scout's obstruction (5) records an ADEQUACY HOLE: `EC1-T006` and
`EC1-T007` together are satisfied by a normalizer that throws the program
away, and the estate closed the analogous hole for `canonServices` with three
PRESERVE laws (`Cas/Backend/Canon.lean:259`, `:266`, `:278`, all verified at
those exact lines). The obvious repair — import `mem_keys_canonServices`
(PRESERVE-keys) one level up — is IMPOSSIBLE.

Any normalizer that is renaming-stable and never invents or loses a block
identifier produces a program with NO blocks at all. The reason is structural:
a renaming can push every identifier of `r` above any bound, so a stable `norm`
must return the same thing for a program whose identifiers are disjoint from
`r`'s; PRESERVE-keys then traps the output's keys inside an empty
intersection.

Consequence for the packet: the adequacy law owed for `normalizeRaw` may NOT
be stated on the bound namespace. It must be stated on the FREE namespace and
on structure (`§8`), or modulo renaming. `canonServices`' PRESERVE bundle does
not transfer, and citing it here would be an error. -/

/-! Three arithmetic helpers, stated at `Nat` rather than at `BlockId`.
`omega` does not see through the `BlockId` abbreviation, so the bound-namespace
arithmetic below is routed through these. -/

theorem shift_absurd {k n b : Nat} (hk : k + (n + 1) = b) (hlt : b ≤ n) : False := by omega

theorem lt_self_absurd {n m : Nat} (h : m + n + 1 < n) : False := by omega

theorem add_cancel_succ {a b n : Nat} (h : a + n + 1 = b + n + 1) : a = b := by omega

def maxKey (r : RawProgram) : Nat := (keys r).foldr max 0

theorem le_foldr_max {l : List Nat} {b : Nat} (h : b ∈ l) : b ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons c t ih =>
    rcases List.mem_cons.mp h with h1 | h2
    · subst h1; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h2) (Nat.le_max_right _ _)

theorem le_maxKey {r : RawProgram} {b : BlockId} (h : b ∈ keys r) : b ≤ maxKey r :=
  le_foldr_max h

theorem shift_injective (n : Nat) : Function.Injective (fun b : BlockId => b + n) := by
  intro a b h
  exact Nat.add_right_cancel h

/-- **The obstruction.** `hrow` is exactly renaming stability — the row, by
`row_iff_renaming_stable`. `hpres` is `mem_keys_canonServices`' forward half at
this carrier. Together they force every normalized program to be empty. -/
theorem preserve_keys_is_incompatible_with_the_row
    (norm : RawProgram → RawProgram)
    (hrow : ∀ f : BlockId → BlockId, Function.Injective f →
        ∀ r, norm (applyRenaming f r) = norm r)
    (hpres : ∀ r, ∀ b ∈ keys (norm r), b ∈ keys r)
    (r : RawProgram) : keys (norm r) = [] := by
  cases hcase : keys (norm r) with
  | nil => rfl
  | cons b t =>
    exfalso
    have hb : b ∈ keys (norm r) := by rw [hcase]; exact List.Mem.head t
    have hlt : b ≤ maxKey r := le_maxKey (hpres r b hb)
    have hb2 : b ∈ keys (norm (applyRenaming (fun x => x + (maxKey r + 1)) r)) := by
      rw [hrow _ (shift_injective (maxKey r + 1)) r]; exact hb
    have hmem := hpres _ b hb2
    rw [keys_applyRenaming] at hmem
    obtain ⟨k, _, hk⟩ := List.mem_map.mp hmem
    exact shift_absurd hk hlt

/-- The concrete consequence for this file's own normalizer: it satisfies the
row, so it CANNOT preserve keys. Renumbering is not a defect to be repaired by
importing `mem_keys_canonServices`; it is forced. -/
theorem normalizeRaw_is_not_key_preserving :
    ¬ ∀ r, ∀ b ∈ keys (normalizeRaw r), b ∈ keys r := by
  intro hpres
  have hempty := preserve_keys_is_incompatible_with_the_row normalizeRaw
    (fun f hf r => normalizeRaw_rename hf r) hpres two
  exact absurd hempty (by decide)

/-- The same statement in the form the packet would actually meet it: a
normalizer cannot be renaming-stable, key-preserving, and non-trivial. -/
theorem no_key_preserving_renaming_stable_normalizer :
    ¬ ∃ norm : RawProgram → RawProgram,
        (∀ f : BlockId → BlockId, Function.Injective f →
          ∀ r, norm (applyRenaming f r) = norm r)
        ∧ (∀ r, ∀ b ∈ keys (norm r), b ∈ keys r)
        ∧ keys (norm two) ≠ [] := by
  rintro ⟨norm, hrow, hpres, hne⟩
  exact hne (preserve_keys_is_incompatible_with_the_row norm hrow hpres two)

/-! ## §8 — the adequacy law that IS compatible: normalization soundness

The `lean-model-invariants` stage names "normalization soundness and
idempotence" as the obligation pair for a `Canonical form + normalizer`
representation. §7 shows idempotence-plus-order-blindness is not enough and
that key preservation is unavailable, so soundness is where the content has to
go: `normalizeRaw r` must BE `r`, renamed. That kills the discarding
normalizer, and it delivers `EC1-T006` as a corollary. -/

/-- `EC1-D021`, modelled: the clauses this section actually needs. Duplicate
keys and dangling successors are what it excludes; both are representable
without it (`ALGEBRA.md:240-243`). -/
structure ProgramWF (r : RawProgram) : Prop where
  keysNodup : (keys r).Nodup
  entryDeclared : r.entry ∈ keys r
  succsDeclared : ∀ kv ∈ r.blocks, ∀ b ∈ kv.2.succs, b ∈ keys r

theorem mem_keys_of_mem_blocks {r : RawProgram} {kv : BlockId × RawBlock}
    (h : kv ∈ r.blocks) : kv.1 ∈ keys r :=
  List.mem_map.mpr ⟨kv, h, rfl⟩

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

theorem idx_lt_length_of_mem {l : List BlockId} {a : BlockId} (h : a ∈ l) :
    idx a l < l.length := by
  induction l with
  | nil => simp at h
  | cons c t ih =>
    rw [idx, List.length_cons]
    by_cases hc : c = a
    · rw [if_pos hc]; omega
    · rw [if_neg hc]
      rcases List.mem_cons.mp h with h1 | h2
      · exact absurd h1.symm hc
      · have := ih h2; omega

theorem idx_inj_of_nodup : ∀ {l : List BlockId}, l.Nodup →
    ∀ {a b : BlockId}, a ∈ l → b ∈ l → idx a l = idx b l → a = b := by
  intro l
  induction l with
  | nil => intro _ a b ha; simp at ha
  | cons c t ih =>
    intro hnd a b ha hb heq
    obtain ⟨hcn, htn⟩ := List.nodup_cons.mp hnd
    rw [idx, idx] at heq
    by_cases h1 : c = a
    · by_cases h2 : c = b
      · rw [← h1, ← h2]
      · rw [if_pos h1, if_neg h2] at heq
        exact absurd heq.symm (Nat.succ_ne_zero _)
    · by_cases h2 : c = b
      · rw [if_neg h1, if_pos h2] at heq
        exact absurd heq (Nat.succ_ne_zero _)
      · rw [if_neg h1, if_neg h2] at heq
        have ha' : a ∈ t := (List.mem_cons.mp ha).resolve_left (fun h => h1 h.symm)
        have hb' : b ∈ t := (List.mem_cons.mp hb).resolve_left (fun h => h2 h.symm)
        exact ih htn ha' hb' (by omega)

/-- The renaming that witnesses soundness. On declared identifiers it IS
`canonId`; everything else is pushed above the table so the function is
globally injective. Note it cannot be renaming-EQUIVARIANT off the table —
that is exactly why `canonId` collapses undeclared identifiers, and why §9's
completeness witness works. -/
def canonWitness (r : RawProgram) : BlockId → BlockId :=
  fun b => if b ∈ keys r then idx b (keys r) else b + (keys r).length + 1

theorem canonWitness_injective {r : RawProgram} (h : (keys r).Nodup) :
    Function.Injective (canonWitness r) := by
  intro a b hab
  unfold canonWitness at hab
  by_cases ha : a ∈ keys r
  · by_cases hb : b ∈ keys r
    · rw [if_pos ha, if_pos hb] at hab
      exact idx_inj_of_nodup h ha hb hab
    · rw [if_pos ha, if_neg hb] at hab
      have hlt := idx_lt_length_of_mem ha
      rw [hab] at hlt
      exact absurd hlt (fun hc => lt_self_absurd hc)
  · by_cases hb : b ∈ keys r
    · rw [if_neg ha, if_pos hb] at hab
      have hlt := idx_lt_length_of_mem hb
      rw [← hab] at hlt
      exact absurd hlt (fun hc => lt_self_absurd hc)
    · rw [if_neg ha, if_neg hb] at hab
      exact add_cancel_succ hab

/-- **Normalization soundness.** On a well-formed program, `normalizeRaw r` is
`r` with its bound namespace injectively renamed — it drops nothing, invents
nothing, and moves no free key. This is the adequacy law §7 leaves available. -/
theorem normalizeRaw_renames_input {r : RawProgram} (h : ProgramWF r) :
    Renames r (normalizeRaw r) := by
  refine ⟨canonWitness r, canonWitness_injective h.keysNodup, ?_⟩
  rw [normalizeRaw_def]
  refine applyRenaming_congr_on r ?_ ?_ ?_
  · simp only [canonWitness, canonId, if_pos h.entryDeclared]
  · intro kv hkv
    simp only [canonWitness, canonId, if_pos (mem_keys_of_mem_blocks hkv)]
  · intro kv hkv b hb
    simp only [canonWitness, canonId, if_pos (h.succsDeclared kv hkv b hb)]

/-- The normalizer the row alone cannot exclude: it discards the program. -/
def discard : RawProgram → RawProgram := fun _ => { entry := 0, blocks := [] }

/-- `EC1-T006` and `EC1-T007` are BOTH satisfied by it — the adequacy hole,
at this carrier. -/
theorem discard_satisfies_T006_and_T007 :
    (∀ r, discard (discard r) = discard r)
      ∧ (∀ f : BlockId → BlockId, Function.Injective f →
          ∀ r, discard (applyRenaming f r) = discard r) :=
  ⟨fun _ => rfl, fun _ _ _ => rfl⟩

/-- And soundness is what closes it. -/
theorem discard_is_not_sound : ¬ Renames two (discard two) := by
  rintro ⟨f, _, heq⟩
  have h := congrArg (fun p => p.blocks.length) heq
  simp [applyRenaming, discard, two] at h

/-- **`EC1-T006` as a corollary, on well-formed programs.** Idempotence is not
this row's obligation — it is `EC1-T006`, another row — but once soundness and
the row are both in hand it costs nothing, which is evidence the bundle is
coherent rather than merely green. -/
theorem normalizeRaw_idempotent_of_wf {r : RawProgram} (h : ProgramWF r) :
    normalizeRaw (normalizeRaw r) = normalizeRaw r := by
  obtain ⟨f, hf, heq⟩ := normalizeRaw_renames_input h
  calc normalizeRaw (normalizeRaw r) = normalizeRaw (applyRenaming f r) := by rw [heq]
    _ = normalizeRaw r := normalizeRaw_rename hf r

/-! ## §9 — non-vacuity, and the completeness half REFUTED

The row is only worth its receipt if its hypothesis is satisfiable
non-trivially and its conclusion is not universally true. Both are checked.

The third witness is the sharp one. The scout's recommended bundle asks for a
completeness half, `normalizeRaw r = normalizeRaw s -> AlphaEq r s`, by
analogy with `EC1-T002`'s IFF. Premise-free it is FALSE, and the reason is
§8's: renaming stability forces `normalizeRaw` to send every undeclared
identifier to one slot, so two programs whose dangling references differ in
MULTIPLICITY share a normal form without being alpha-equivalent. That witness
also proves `AlphaEq` is not normal-form equality, which is the §3 escape. -/

def one : RawProgram := { entry := 0, blocks := [(0, blkA)] }

/-- The hypothesis is satisfiable non-trivially: two DISTINCT programs are
alpha-equivalent. -/
theorem alphaEq_is_not_equality :
    AlphaEq two (applyRenaming (swapId 0 1) two) ∧ two ≠ applyRenaming (swapId 0 1) two :=
  ⟨⟨swapId 0 1, swapId 0 1, swapId_isRenaming 0 1, rfl⟩, by decide⟩

/-- The conclusion is not universally true: `normalizeRaw` separates. -/
theorem normalizeRaw_separates : normalizeRaw one ≠ normalizeRaw two := by decide

/-- Two programs with one dangling successor each, differing only in how many
times the dangling identifier is repeated. -/
def dangleL : RawProgram := { entry := 0, blocks := [(0, { op := "a", succs := [7, 8] })] }
def dangleR : RawProgram := { entry := 0, blocks := [(0, { op := "a", succs := [7, 7] })] }

theorem dangle_same_normal_form : normalizeRaw dangleL = normalizeRaw dangleR := by decide

theorem dangle_not_alphaEq : ¬ AlphaEq dangleL dangleR := by
  rintro ⟨f, g, hfg, heq⟩
  simp only [applyRenaming, dangleL, dangleR, RawBlock.rename, List.map_cons,
    List.map_nil, RawProgram.mk.injEq, List.cons.injEq, Prod.mk.injEq,
    RawBlock.mk.injEq, and_true, true_and] at heq
  obtain ⟨-, -, h7, h8⟩ := heq
  have : (7 : Nat) = 8 := hfg.injective (h7.trans h8.symm)
  exact absurd this (by decide)

/-- **The completeness half is FALSE without a well-formedness premise.**
`normalizeRaw` is sound (§8) but not complete: equal normal forms do not imply
alpha-equivalence. This is a candidate register row against the scouted
`normalizeRaw_alpha_complete`, not merely a note. -/
theorem completeness_is_false_premise_free :
    ¬ ∀ r s : RawProgram, normalizeRaw r = normalizeRaw s → AlphaEq r s :=
  fun h => dangle_not_alphaEq (h dangleL dangleR dangle_same_normal_form)

/-- Consequently `AlphaEq` is NOT normal-form equality at this carrier: it is
strictly finer. The §3 trap is escaped by a witness, not by a convention. -/
theorem alphaEq_is_not_normal_form_equality :
    ¬ ∀ r s : RawProgram, (normalizeRaw r = normalizeRaw s) ↔ AlphaEq r s :=
  fun h => dangle_not_alphaEq ((h dangleL dangleR).mp dangle_same_normal_form)

/-! ## §10 — divergence from the DAG signature, itemised

`EC1-T007` as written: `alphaEq r s -> normalizeRaw r = normalizeRaw s`,
depending on `D2` and `EC1-T006`.

1. **`alphaEq` promoted to a declared relation.** It is `AlphaEq`, defined by a
   bijective renaming action, with no mention of `normalizeRaw`.
   `canon_equiv_reading_is_iff_rfl` shows the alternative spelling — the
   estate's own `Cas.Canonicalizer.Equiv` — makes the row `Iff.rfl`, and
   `alphaEq_is_not_normal_form_equality` shows this declaration escapes it.

2. **Bijectivity spelled as a two-sided inverse, and the row needs only
   injectivity.** `Function.Bijective` does not exist in this toolchain
   (verified; `library/cas` has an empty `.lake/packages`, no Mathlib). More
   substantively, `normalizeRaw_renames` proves the conclusion from
   `Renames` — an injection — and `AlphaEq` is a strictly stronger premise.
   Surjectivity is used ONLY to make `AlphaEq` symmetric (`AlphaEq.symm`).
   `injectivity_is_necessary` proves injectivity itself cannot be dropped.
   NET: STRONGER than the scouted statement on this axis.

3. **The scouted `ProgramWF r` premise is DROPPED.** The scout transferred
   `EC1-CE030` "by shape, flagged as such" and did not prove the transfer. It
   does not fire. CE030 attacks a LAST-WINS keyed normalizer; §7 proves that no
   key-preserving renaming-stable normalizer exists at all, and a sort-by-key
   normalizer is refuted by the scout's own `swapKey` witness, so the CE030
   shape is not merely premise-hungry here — it is unavailable. A
   presentation-order renumbering needs no duplicate-free premise, and none is
   used. NET: STRONGER on this axis.

4. **One bound namespace, not three.** The scout's `Renaming` carries
   `block`/`code`/`region`. This file models `block` only. The three act on
   disjoint occurrence sets and the argument is componentwise, but that is
   NOT proved here. NET: WEAKER on this axis — see `checksOmitted`.

5. **`normalizeRaw` is concrete, not the packet's declared term.** It is a
   presentation-order renumbering. The row is proved ABOUT THIS FUNCTION. Any
   `EC1-D026` that sorts the block table by identifier is refuted, not
   supported, by this file (§7 plus the scout's `swapKey` witness).

6. **The stated dependency `EC1-T006` is not used and cannot help.**
   `T006_does_not_imply_T007`. The real dependency is
   `normalizeRaw_rename`, which has no DAG row. Conversely `EC1-T006` follows
   from this row plus soundness on well-formed programs
   (`normalizeRaw_idempotent_of_wf`), so the DAG's edge points the wrong way.

7. **Two obligations the packet does not carry are established here.**
   `preserve_keys_is_incompatible_with_the_row` (the PRESERVE bundle at
   `Cas/Backend/Canon.lean:259/266/278` does NOT transfer to a bound
   namespace) and `completeness_is_false_premise_free` (the scouted
   `normalizeRaw_alpha_complete` is false without well-formedness). Both are
   candidate `EC1-CE` register rows; no ID is minted here.
-/

/-! ## §11 — checks OMITTED

Stated so the receipt is not read for more than it says.

* **Three bound namespaces reduced to one.** `EC1-A11` renames `BlockId`,
  `CodeId` and `RegionId`. Only `BlockId` is modelled. The three act on
  disjoint occurrence sets so the argument should be componentwise, but that
  is NOT proved here and no product `Renaming` structure is built.
* **Eight tables reduced to one.** `pureTable`, `foreignTable`, `handlerTable`,
  `codeTable`, `regionTable`, `declaredAER`, `publicSurface` and
  `alphabetVersion` are absent. `presentation` in particular is absent, and it
  is the one that matters: `ALGEBRA.md:237` gives `RawProgram` a source-span
  map KEYED BY the identifiers a renaming moves, so a real `normalizeRaw` must
  normalize or erase it. `EC1-T013 check_erase` feels the same choice. Not
  probed.
* **Reachability is not modelled.** The scout named a renumbering driven by
  reachability from `entry`. This file renumbers by PRESENTATION order
  (`EFFECTS-BACKEND` R4). For the row the two are interchangeable — both are
  renaming-equivariant and the proof obligation has the same shape — but a
  reachability-driven normalizer additionally DROPS unreachable blocks, which
  collides with `EC1-T013` and is not analysed here.
* **No completeness theorem is supplied.** §9 refutes the premise-free form.
  Whether `ProgramWF r -> ProgramWF s -> normalizeRaw r = normalizeRaw s ->
  AlphaEq r s` holds is OPEN; the witness that kills the premise-free form is
  a dangling reference, which `ProgramWF` excludes, so the restricted form is
  not refuted by anything here.
* **`EC1-T006` is proved only under `ProgramWF`.** Idempotence is another
  row's obligation and unconditional idempotence of this `normalizeRaw` was
  not attempted.
* **Nothing about `EC1-D026`.** Every theorem is about the concrete
  `normalizeRaw` defined in §4. A successful elaboration here proves the
  stated propositions about THIS function; it is not model assurance, not
  implementation assurance, and it does not close `EC1-T007`.
* **No lake target was built.** Only `lake env lean` on this single
  out-of-target file. Nothing under `library/`, `formal/`, or any packet `.md`
  was read-modify-written.
* **`EC1-CE031`, `EC1-CE032`, `EC1-CE033` were read and do not bear on this
  row** (they attack `EC1-T015`, `EC1-T088`, `EC1-T100`). `EC1-CE030` bears
  and is discharged rather than inherited: see `§10` divergence 3.
-/

end EffectCoreV1.T007

/-! ## Kernel receipts

`#print axioms` on every theorem. No `sorry`, no `axiom`, no `native_decide`,
no `#eval` carrying a claim. The `Classical.choice`-free ceiling is deliberate:
`List.idxOf`'s `BEq`/`LawfulBEq` route pulls `Classical.choice` into every
downstream receipt, which is why §4 uses the local `idx`. -/

#print axioms EffectCoreV1.T007.IsRenaming.injective
#print axioms EffectCoreV1.T007.applyRenaming_id
#print axioms EffectCoreV1.T007.applyRenaming_comp
#print axioms EffectCoreV1.T007.applyRenaming_congr
#print axioms EffectCoreV1.T007.keys_applyRenaming
#print axioms EffectCoreV1.T007.alphaEq_renames
#print axioms EffectCoreV1.T007.AlphaEq.refl
#print axioms EffectCoreV1.T007.AlphaEq.symm
#print axioms EffectCoreV1.T007.AlphaEq.trans
#print axioms EffectCoreV1.T007.canon_equiv_reading_is_iff_rfl
#print axioms EffectCoreV1.T007.normal_form_reading_makes_the_row_free
#print axioms EffectCoreV1.T007.idx_map
#print axioms EffectCoreV1.T007.canonId_applyRenaming
#print axioms EffectCoreV1.T007.normalizeRaw_rename
#print axioms EffectCoreV1.T007.normalizeRaw_renames
#print axioms EffectCoreV1.T007.normalizeRaw_alpha
#print axioms EffectCoreV1.T007.row_iff_renaming_stable
#print axioms EffectCoreV1.T007.injectivity_is_necessary
#print axioms EffectCoreV1.T007.row_is_false_without_injectivity
#print axioms EffectCoreV1.T007.swapOp_involutive
#print axioms EffectCoreV1.T007.swapOp_injective
#print axioms EffectCoreV1.T007.free_namespace_refutes_the_row
#print axioms EffectCoreV1.T007.swapId_involutive
#print axioms EffectCoreV1.T007.swapId_isRenaming
#print axioms EffectCoreV1.T007.swapId_injective
#print axioms EffectCoreV1.T007.T006_does_not_imply_T007
#print axioms EffectCoreV1.T007.le_foldr_max
#print axioms EffectCoreV1.T007.le_maxKey
#print axioms EffectCoreV1.T007.shift_injective
#print axioms EffectCoreV1.T007.preserve_keys_is_incompatible_with_the_row
#print axioms EffectCoreV1.T007.normalizeRaw_is_not_key_preserving
#print axioms EffectCoreV1.T007.no_key_preserving_renaming_stable_normalizer
#print axioms EffectCoreV1.T007.mem_keys_of_mem_blocks
#print axioms EffectCoreV1.T007.applyRenaming_congr_on
#print axioms EffectCoreV1.T007.idx_lt_length_of_mem
#print axioms EffectCoreV1.T007.idx_inj_of_nodup
#print axioms EffectCoreV1.T007.canonWitness_injective
#print axioms EffectCoreV1.T007.normalizeRaw_renames_input
#print axioms EffectCoreV1.T007.discard_satisfies_T006_and_T007
#print axioms EffectCoreV1.T007.discard_is_not_sound
#print axioms EffectCoreV1.T007.normalizeRaw_idempotent_of_wf
#print axioms EffectCoreV1.T007.alphaEq_is_not_equality
#print axioms EffectCoreV1.T007.normalizeRaw_separates
#print axioms EffectCoreV1.T007.dangle_same_normal_form
#print axioms EffectCoreV1.T007.dangle_not_alphaEq
#print axioms EffectCoreV1.T007.completeness_is_false_premise_free
#print axioms EffectCoreV1.T007.alphaEq_is_not_normal_form_equality
