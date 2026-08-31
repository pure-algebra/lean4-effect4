import Cas.Core.Admission
import Cas.Backend.Canon
import Cas.Lang.Defun
import Cas.Lift.Decode

/-!
# BREAKER attack witnesses against `workshop/s2/T014.lean` (`EC1-T014`)

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s2/attack-EC1-T014.lean
```

Skill stage: `.claude/skills/lean/workflows/lean-assurance-review/SKILL.md`.
Gate passed: `lake env lean` on the target (49 receipts, no `sorry`/`axiom`/
`native_decide`) and on this file. Nothing under `library/`,
`formal/effect-core-v1/` or any packet `.md` is touched.

## What is attacked

The target's headline is not `erase_wf` (it concedes that row is a field
projection). Its headline results are:

* finding (1) — `T010`/`T013` are "UNMENTIONABLE" in `EC1-T014`, so the row
  should be DELETED;
* finding (5)/§8 — `erase_wf_designB_is_false` and
  `normalizer_does_not_preserve_wf`: carrier design (b) is REFUTED;
* finding (6)/§9 — `CONTRACT-PACKET.md:309` is a projection of "clause 12",
  and `normalizeChecked` needs no declaration.

All three rest on two clause definitions the target introduced. §1-§3 below
show both are SUBSTITUTIONS for what `ALGEBRA.md` says and for what all four
sibling `EC1-S2` implementers wrote, and that replacing either one with the
sibling reading kills the corresponding result. §4 refutes finding (1)
outright against `ALGEBRA.md:320-321`.

## The two substituted clauses

`ALGEBRA.md:314-315`, clause 10, verbatim:

> 10. `EntryWF`: the entry accepts exactly its declared input and every normal
>     return has result type `A`;

A type-agreement clause about the entry's interface. The target models it as
`EntryWF r := (blockIds r).head? = some r.entry` — the entry sits at table
POSITION ZERO. The four siblings that model the clause all read it by
LOOKUP/MEMBERSHIP, never by position:

| file | `EntryWF` |
| --- | --- |
| `T010.lean:660` | `(∃ b, r.blockOf r.entry = some b ∧ b.params = [r.entryTy]) ∧ ∀ b ∈ r.blocks, CloseOk r b.term` |
| `T011.lean:246` | `Declared r.blocks r.entry` |
| `T012.lean:494` | `r.entry ∈ r.blocks.map (·.id)` |
| `T013.lean:368` | `r.entry ∈ r.ids` |
| `T014.lean` (target) | `(blockIds r).head? = some r.entry` |

`ALGEBRA.md:317`, clause 12, verbatim:

> 12. `PresentationWF`: normalization does not change reference meaning.

A clause about reference MEANING surviving normalization. The target models it
as `CanonWF r := normalizeRaw r = r` — the raw value is already a fixed point.
`T010.lean:725` models the same clause as
`PresentationWFsyn r := ∀ b ∈ r.blocks, (normalizeRaw r).blockOf b.id = r.blockOf b.id`,
which is the reading `ALGEBRA.md:317` states and is invariant under
reordering.

Every result below is elaborated; `#print axioms` on all of them at the end.
-/

namespace AttackT014

open Cas Cas.Lang

/-! ## §0 — the target's carrier, transcribed verbatim

Copied from `workshop/s2/T014.lean` §1-§4 so the counterexamples land on the
same objects. Nothing here is changed; the additions start at §1. -/

structure Env where
  registry : List UInt8
  deriving DecidableEq

inductive Term where
  | close
  | jump (dst : Nat)
  deriving DecidableEq

def Term.targets : Term → List Nat
  | .close => []
  | .jump d => [d]

structure Block where
  id : Nat
  body : PProg
  foreign : List UInt8
  term : Term
  deriving DecidableEq

structure RawProgram where
  entry : Nat
  blocks : List Block
  deriving DecidableEq

def blockIds (r : RawProgram) : List Nat := r.blocks.map Block.id

def insertById (b : Block) : List Block → List Block
  | [] => [b]
  | c :: rest => if b.id ≤ c.id then b :: c :: rest else c :: insertById b rest

def sortBlocks : List Block → List Block
  | [] => []
  | b :: rest => insertById b (sortBlocks rest)

def normalizeRaw (r : RawProgram) : RawProgram :=
  { r with blocks := sortBlocks r.blocks }

inductive Diagnostic where
  | ids (dup : Option Nat)
  | refs (bad : Option Nat)
  | lines (blk : Option Nat)
  | foreign (fid : Option UInt8)
  | entry (declared : Nat) (first : Option Nat)
  | canon
  deriving DecidableEq

def nodupB : List Nat → Bool
  | [] => true
  | a :: as => !as.contains a && nodupB as

def NoDupIds : List Nat → Prop
  | [] => True
  | a :: as => a ∉ as ∧ NoDupIds as

theorem nodupB_iff : ∀ l : List Nat, nodupB l = true ↔ NoDupIds l
  | [] => by simp [nodupB, NoDupIds]
  | a :: as => by simp [nodupB, NoDupIds, nodupB_iff as]

def findDupId : List Nat → Option Nat
  | [] => none
  | a :: as => if as.contains a then some a else findDupId as

def refsB (r : RawProgram) : Bool :=
  r.blocks.all fun b => b.term.targets.all fun t => (blockIds r).contains t

def RefsWF (r : RawProgram) : Prop :=
  ∀ b ∈ r.blocks, ∀ t ∈ b.term.targets, t ∈ blockIds r

theorem refsB_iff (r : RawProgram) : refsB r = true ↔ RefsWF r := by
  simp [refsB, RefsWF, List.all_eq_true]

def findBadJump (r : RawProgram) : Option Nat :=
  r.blocks.findSome? fun b => b.term.targets.find? fun t => !(blockIds r).contains t

def pinB : PIn → Bool
  | .lit _ => true
  | .ans i => decide (i < 4294967296)

theorem pinB_iff (i : PIn) : pinB i = true ↔ i.WF := by
  cases i <;> simp [pinB, PIn.WF]

def plineB : PLine → Bool
  | .put _ _ payload refs =>
      decide (payload.length < 4294967296) && decide (refs.length < 4294967296) &&
        refs.all fun r => pinB r.2
  | .load src => pinB src

theorem plineB_iff (l : PLine) : plineB l = true ↔ l.WF := by
  cases l with
  | put v t payload refs =>
      simp [plineB, PLine.WF, List.all_eq_true, pinB_iff, and_assoc]
  | load src => simpa [plineB, PLine.WF] using pinB_iff src

def linesB (r : RawProgram) : Bool := r.blocks.all fun b => b.body.all plineB

def LinesWF (r : RawProgram) : Prop := ∀ b ∈ r.blocks, ∀ l ∈ b.body, l.WF

theorem linesB_iff (r : RawProgram) : linesB r = true ↔ LinesWF r := by
  simp [linesB, LinesWF, List.all_eq_true, plineB_iff]

def findBadBlock (r : RawProgram) : Option Nat :=
  (r.blocks.find? fun b => !b.body.all plineB).map Block.id

def foreignB (rho : Env) (r : RawProgram) : Bool :=
  r.blocks.all fun b => b.foreign.all fun f => rho.registry.contains f

def ForeignWF (rho : Env) (r : RawProgram) : Prop :=
  ∀ b ∈ r.blocks, ∀ f ∈ b.foreign, f ∈ rho.registry

theorem foreignB_iff (rho : Env) (r : RawProgram) :
    foreignB rho r = true ↔ ForeignWF rho r := by
  simp [foreignB, ForeignWF, List.all_eq_true]

def findBadForeign (rho : Env) (r : RawProgram) : Option UInt8 :=
  r.blocks.findSome? fun b => b.foreign.find? fun f => !rho.registry.contains f

/-- The target's clause 10. POSITIONAL. -/
def EntryWF (r : RawProgram) : Prop := (blockIds r).head? = some r.entry

def entryB (r : RawProgram) : Bool := decide ((blockIds r).head? = some r.entry)

theorem entryB_iff (r : RawProgram) : entryB r = true ↔ EntryWF r := by
  simp [entryB, EntryWF]

/-- The target's clause 12. FIXED-POINT. -/
def CanonWF (r : RawProgram) : Prop := normalizeRaw r = r

def canonB (r : RawProgram) : Bool := decide (normalizeRaw r = r)

theorem canonB_iff (r : RawProgram) : canonB r = true ↔ CanonWF r := by
  simp [canonB, CanonWF]

def ProgramWFcore (rho : Env) (r : RawProgram) : Prop :=
  NoDupIds (blockIds r) ∧ RefsWF r ∧ LinesWF r ∧ ForeignWF rho r ∧ EntryWF r

def ProgramWF (rho : Env) (r : RawProgram) : Prop :=
  ProgramWFcore rho r ∧ CanonWF r

def firstError : List (Bool × Diagnostic) → Except Diagnostic Unit
  | [] => .ok ()
  | (b, d) :: rest => if b then firstError rest else .error d

theorem firstError_ok_iff :
    ∀ l : List (Bool × Diagnostic), firstError l = .ok () ↔ ∀ p ∈ l, p.1 = true
  | [] => by simp [firstError]
  | (b, d) :: rest => by
      cases b with
      | false => simp [firstError]
      | true => simp [firstError, firstError_ok_iff rest]

def clauseList (rho : Env) (r : RawProgram) : List (Bool × Diagnostic) :=
  [ (nodupB (blockIds r), .ids (findDupId (blockIds r)))
  , (refsB r,             .refs (findBadJump r))
  , (linesB r,            .lines (findBadBlock r))
  , (foreignB rho r,      .foreign (findBadForeign rho r))
  , (entryB r,            .entry r.entry (blockIds r).head?)
  , (canonB r,            .canon) ]

def checkClauses (rho : Env) (r : RawProgram) : Except Diagnostic Unit :=
  firstError (clauseList rho r)

theorem clauses_sound {rho : Env} {r : RawProgram}
    (h : checkClauses rho r = .ok ()) : ProgramWF rho r := by
  have h6 := (firstError_ok_iff (clauseList rho r)).mp h
  simp only [clauseList, List.forall_mem_cons] at h6
  obtain ⟨e1, e2, e3, e4, e5, e6, -⟩ := h6
  exact ⟨⟨(nodupB_iff _).mp e1, (refsB_iff _).mp e2, (linesB_iff _).mp e3,
          (foreignB_iff _ _).mp e4, (entryB_iff _).mp e5⟩, (canonB_iff _).mp e6⟩

theorem clauses_complete {rho : Env} {r : RawProgram}
    (h : ProgramWF rho r) : checkClauses rho r = .ok () := by
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩ := h
  refine (firstError_ok_iff (clauseList rho r)).mpr ?_
  simp only [clauseList, List.forall_mem_cons]
  exact ⟨(nodupB_iff _).mpr h1, (refsB_iff _).mpr h2, (linesB_iff _).mpr h3,
         (foreignB_iff _ _).mpr h4, (entryB_iff _).mpr h5, (canonB_iff _).mpr h6,
         by simp⟩

abbrev AER := Nat

def synthAER (r : RawProgram) : AER := r.blocks.length

structure CheckedProgram (rho : Env) (aer : AER) where
  raw : RawProgram
  wf : ProgramWF rho raw
  aerOk : synthAER raw = aer

def erase {rho : Env} {aer : AER} (p : CheckedProgram rho aer) : RawProgram := p.raw

def check (rho : Env) (r : RawProgram) :
    Except Diagnostic (Σ aer, CheckedProgram rho aer) :=
  match hc : checkClauses rho r with
  | .error d => .error d
  | .ok ()   => .ok ⟨synthAER r, ⟨r, clauses_sound hc, rfl⟩⟩

theorem check_sound {rho : Env} {r : RawProgram} {x : Σ aer, CheckedProgram rho aer}
    (h : check rho r = .ok x) : ProgramWF rho r := by
  unfold check at h
  split at h
  · exact nomatch h
  · rename_i hc; exact clauses_sound hc

def demoEnv : Env := ⟨[7]⟩

def demoRaw : RawProgram :=
  { entry := 0, blocks := [⟨0, [PLine.load (.ans 0)], [7], .close⟩] }

theorem demo_accepts : checkClauses demoEnv demoRaw = .ok () := rfl

/-- The target's design-(b) witness, transcribed. -/
def badOrderRaw : RawProgram :=
  { entry := 5, blocks := [⟨5, [], [], .close⟩, ⟨1, [], [], .close⟩] }

/-! ### Transcription-fidelity receipts

Three of the target's own theorems, restated verbatim against the
transcription above. If §0 had drifted from `T014.lean`, these would fail. -/

theorem fidelity_badOrder_core : ProgramWFcore demoEnv badOrderRaw :=
  ⟨(nodupB_iff _).mp rfl, (refsB_iff _).mp rfl, (linesB_iff _).mp rfl,
   (foreignB_iff _ _).mp rfl, (entryB_iff _).mp rfl⟩

theorem fidelity_badOrder_normalized_entryB_false :
    entryB (normalizeRaw badOrderRaw) = false := rfl

theorem fidelity_badOrder_refused :
    checkClauses demoEnv badOrderRaw = .error .canon := rfl

def fidelity_badLineRaw : RawProgram :=
  { entry := 0, blocks := [⟨0, [PLine.load (.ans 4294967296)], [], .close⟩] }

theorem fidelity_badLine_rejected :
    checkClauses demoEnv fidelity_badLineRaw = .error (.lines (some 0)) := rfl

def fidelity_badForeignRaw : RawProgram :=
  { entry := 0, blocks := [⟨0, [], [9], .close⟩] }

theorem fidelity_badForeign_rejected :
    checkClauses demoEnv fidelity_badForeignRaw = .error (.foreign (some 9)) := rfl

/-! ## §1 — permutation invariance, and what the positional clause costs

`normalizeRaw` is a PERMUTATION of the block table. Everything the target's
core judgment says, other than its positional entry clause, is invariant under
permutation. That is the whole content of §8's "refutation" of design (b). -/

theorem insertById_perm (b : Block) :
    ∀ l : List Block, (insertById b l).Perm (b :: l)
  | [] => by simp [insertById]
  | c :: rest => by
      by_cases hb : b.id ≤ c.id
      · simp [insertById, hb]
      · simp only [insertById, hb, if_false]
        exact ((insertById_perm b rest).cons c).trans (List.Perm.swap b c rest)

theorem mem_insertById (b : Block) (l : List Block) (c : Block) :
    c ∈ insertById b l ↔ c = b ∨ c ∈ l :=
  ((insertById_perm b l).mem_iff).trans List.mem_cons

theorem sortBlocks_perm : ∀ l : List Block, (sortBlocks l).Perm l
  | [] => .refl _
  | b :: rest => by
      simp only [sortBlocks]
      exact (insertById_perm b (sortBlocks rest)).trans ((sortBlocks_perm rest).cons b)

theorem normalizeRaw_perm (r : RawProgram) : (normalizeRaw r).blocks.Perm r.blocks :=
  sortBlocks_perm r.blocks

theorem normalizeRaw_entry (r : RawProgram) : (normalizeRaw r).entry = r.entry := rfl

theorem blockIds_perm (r : RawProgram) : (blockIds (normalizeRaw r)).Perm (blockIds r) :=
  (normalizeRaw_perm r).map Block.id

/-- The target's `NoDupIds` is `List.Nodup` under another name, so it too is
permutation-invariant. -/
theorem noDupIds_iff_nodup : ∀ l : List Nat, NoDupIds l ↔ l.Nodup
  | [] => by simp [NoDupIds]
  | a :: as => by simp [NoDupIds, List.nodup_cons, noDupIds_iff_nodup as]

/-! ## §2 — BREAK 1: design (b) survives the sibling entry clause

Substitute the entry clause every other `EC1-S2` implementer wrote — and the
one `ALGEBRA.md:314-315` supports, since a clause about the entry's DECLARED
INPUT TYPE is a lookup, not a table position — and
`normalizer_does_not_preserve_wf` is not merely unproved: its negation is
PROVED, for every environment and every raw program. -/

/-- Clause 10 as `T011.lean:246` / `T012.lean:494` / `T013.lean:368` write it. -/
def EntryMem (r : RawProgram) : Prop := r.entry ∈ blockIds r

def ProgramWFcoreMem (rho : Env) (r : RawProgram) : Prop :=
  NoDupIds (blockIds r) ∧ RefsWF r ∧ LinesWF r ∧ ForeignWF rho r ∧ EntryMem r

/-- The obligation the target names at `T014.lean` §8 and declares unowned,
restated at the sibling entry clause. -/
def NormalizerPreservesWFmem (rho : Env) : Prop :=
  ∀ r : RawProgram, ProgramWFcoreMem rho r → ProgramWFcoreMem rho (normalizeRaw r)

/-- **BREAK 1.** The target's `normalizer_does_not_preserve_wf` is an artifact
of its positional entry clause. At the sibling clause the normalizer DOES
preserve well-formedness — proved, not exhibited, for all `rho` and all `r`. -/
theorem normalizer_preserves_wf_at_the_sibling_entry_clause (rho : Env) :
    NormalizerPreservesWFmem rho := by
  intro r h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hp : (blockIds (normalizeRaw r)).Perm (blockIds r) := blockIds_perm r
  have hb : ∀ b : Block, b ∈ (normalizeRaw r).blocks ↔ b ∈ r.blocks :=
    fun b => (normalizeRaw_perm r).mem_iff
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (noDupIds_iff_nodup _).mpr (hp.symm.nodup ((noDupIds_iff_nodup _).mp h1))
  · intro b hbm t htm
    exact hp.mem_iff.mpr (h2 b ((hb b).mp hbm) t htm)
  · intro b hbm l hlm; exact h3 b ((hb b).mp hbm) l hlm
  · intro b hbm f hfm; exact h4 b ((hb b).mp hbm) f hfm
  · show (normalizeRaw r).entry ∈ blockIds (normalizeRaw r)
    rw [normalizeRaw_entry]
    exact hp.mem_iff.mpr h5

/-- Design (b)'s carrier at the sibling entry clause. -/
structure CheckedBmem (rho : Env) where
  raw : RawProgram
  wf : ProgramWFcoreMem rho raw

def eraseBmem {rho : Env} (p : CheckedBmem rho) : RawProgram := normalizeRaw p.raw

/-- **BREAK 1, corollary.** `T014.lean`'s `erase_wf_designB_is_false` is FALSE
of the packet's own clause: at the sibling entry clause, design (b) satisfies
`EC1-T014`. So finding (5) — "the row is FALSE under the other erase design" —
does not survive replacing one substituted clause. -/
theorem erase_wf_designB_holds_at_the_sibling_entry_clause
    (rho : Env) (p : CheckedBmem rho) : ProgramWFcoreMem rho (eraseBmem p) :=
  normalizer_preserves_wf_at_the_sibling_entry_clause rho p.raw p.wf

/-- The target's own witness, surviving. `badOrderRaw` is `ProgramWFcoreMem`
before AND after normalization; only the positional clause condemns it. -/
theorem badOrder_core_mem : ProgramWFcoreMem demoEnv badOrderRaw :=
  ⟨(nodupB_iff _).mp rfl, (refsB_iff _).mp rfl, (linesB_iff _).mp rfl,
   (foreignB_iff _ _).mp rfl, by unfold EntryMem; decide⟩

theorem badOrder_survives_normalization :
    ProgramWFcoreMem demoEnv (normalizeRaw badOrderRaw) :=
  normalizer_preserves_wf_at_the_sibling_entry_clause demoEnv badOrderRaw badOrder_core_mem

/-- And the positional clause is the ONLY thing that kills it: the target's
`badOrder_normalized_not_core` fails at exactly the fifth conjunct. -/
theorem badOrder_normalized_fails_only_the_positional_clause :
    NoDupIds (blockIds (normalizeRaw badOrderRaw)) ∧
    RefsWF (normalizeRaw badOrderRaw) ∧
    LinesWF (normalizeRaw badOrderRaw) ∧
    ForeignWF demoEnv (normalizeRaw badOrderRaw) ∧
    ¬ EntryWF (normalizeRaw badOrderRaw) :=
  ⟨badOrder_survives_normalization.1, badOrder_survives_normalization.2.1,
   badOrder_survives_normalization.2.2.1, badOrder_survives_normalization.2.2.2.1,
   fun h => by
     have hb := (entryB_iff (normalizeRaw badOrderRaw)).mpr h
     have h0 : entryB (normalizeRaw badOrderRaw) = false := rfl
     rw [h0] at hb
     exact Bool.noConfusion hb⟩

/-! ## §3 — BREAK 2: the fixed-point clause 12 is not `ALGEBRA.md:317`'s

`ALGEBRA.md:317` clause 12 is `PresentationWF`: "normalization does not change
reference meaning". `T010.lean:725` models exactly that:
`PresentationWFsyn r := ∀ b ∈ r.blocks, (normalizeRaw r).blockOf b.id = r.blockOf b.id`.
The target instead writes `CanonWF r := normalizeRaw r = r`, which is strictly
stronger and is what makes `badOrder_refused_by_the_canonical_checker` and
`erase_is_normal` work. The two readings disagree on the target's own witness. -/

def blockOf (r : RawProgram) (i : Nat) : Option Block :=
  r.blocks.find? fun b => b.id == i

/-- `ALGEBRA.md:317` clause 12, in `T010.lean:725`'s spelling. -/
def PresentationWFsyn (r : RawProgram) : Prop :=
  ∀ b ∈ r.blocks, blockOf (normalizeRaw r) b.id = blockOf r b.id

/-- **BREAK 2.** The target's witness satisfies the packet's clause 12 and
fails the target's. The refutation in §8 of `T014.lean` therefore runs on a
clause the packet does not state. -/
theorem badOrder_satisfies_packet_clause12 : PresentationWFsyn badOrderRaw := by
  unfold PresentationWFsyn
  decide

/-- The same witness at `T010.lean:660`'s ENTRY clause, which resolves the entry
by LOOKUP: normalization leaves the entry's row untouched. So the lookup reading
of clause 10 survives §8's witness too, not only the membership reading of §2. -/
theorem badOrder_entry_lookup_survives :
    blockOf (normalizeRaw badOrderRaw) badOrderRaw.entry
      = blockOf badOrderRaw badOrderRaw.entry := rfl

theorem badOrder_fails_target_clause12 : ¬ CanonWF badOrderRaw := by
  intro h
  have : canonB badOrderRaw = true := (canonB_iff _).mpr h
  have h0 : canonB badOrderRaw = false := rfl
  rw [h0] at this
  exact Bool.noConfusion this

/-! ## §4 — BREAK 3: `T010` is MENTIONABLE, and necessary

`T014.lean` finding (1): the DAG's dependencies `T010,T013` are "not merely
unnecessary, they are UNMENTIONABLE: nothing in the statement can refer to a
checker", and therefore `EC1-T014` should be deleted as a row.

That conclusion is drawn from `ALGEBRA.md:319-320`, quoted in the target as
"stores an erased raw value, normalized lookup tables, and evidence of
`ProgramWF`". The sentence continues at `ALGEBRA.md:320-321`:

> `EC1-A13 CheckedProgram A E R` stores an erased raw value, normalized lookup
> tables, and evidence of `ProgramWF`. **The only public constructor is a
> checker:**

The target's `CheckedProgram` has a public anonymous constructor, used
directly at its `demoChecked` (`⟨demoRaw, clauses_sound demo_accepts, rfl⟩`)
rather than through `check`. Take the packet's sentence whole and the carrier
below is the one it describes — and `erase_wf` at THAT carrier is not a
projection, because there is no `wf` field to project. Its only route is
`check_sound`, i.e. `EC1-T010`, exactly the edge the DAG draws. -/

/-- `EC1-A13` with `ALGEBRA.md:320-321` honoured: the only introduction rule
is the checker. -/
def CheckedByChecker (rho : Env) : Type :=
  { r : RawProgram // ∃ x : Σ aer, CheckedProgram rho aer, check rho r = .ok x }

def eraseC {rho : Env} (p : CheckedByChecker rho) : RawProgram := p.val

/-- **BREAK 3.** `EC1-T014` at the checker-introduced carrier. `T010` occurs in
the proof, and no field projection is available. The DAG's `T014 <- T010` edge
is CORRECT under the packet's own carrier sentence, and finding (1)'s
"UNMENTIONABLE" claim is refuted. -/
theorem erase_wfC {rho : Env} (p : CheckedByChecker rho) : ProgramWF rho (eraseC p) := by
  obtain ⟨r, x, hx⟩ := p
  exact check_sound hx

/-- The carrier is inhabited, so the statement above is not vacuous. -/
def demoC : CheckedByChecker demoEnv :=
  ⟨demoRaw, ⟨_, rfl⟩⟩

/-- What the target's generalisation actually shows. `Bundled` presumes a
stored `wf` field; the packet's carrier does not have one. So
`erase_wf_needs_no_checker` is a theorem about design (a) only, not about
`EC1-D023`. Here is the honest contrast: with the field REMOVED, the same
proposition is not provable from the carrier alone — it needs a soundness
premise, which is `T010`. -/
theorem erase_wfC_needs_soundness
    {Raw : Type} {WF : Raw → Prop} {Ok : Raw → Prop}
    (sound : ∀ r, Ok r → WF r) (p : { r : Raw // Ok r }) : WF p.val :=
  sound p.val p.property

/-! ## §5 — BREAK 4: the target's `ProgramWF` refuses well-formed programs

The two substituted clauses do not merely manufacture §8's refutation; they
CONFLICT. `CanonWF` orders the table by block ID and `EntryWF` demands the
entry at position zero, so the conjunction forces the entry block to carry the
LEAST ID in the program. Nothing in `ALGEBRA.md:297-318` asks for that. -/

def SortedIds : List Block → Prop
  | [] => True
  | b :: rest => (∀ c ∈ rest, b.id ≤ c.id) ∧ SortedIds rest

theorem insertById_sorted (b : Block) :
    ∀ l : List Block, SortedIds l → SortedIds (insertById b l)
  | [], _ => by
      show SortedIds [b]
      exact ⟨by simp, trivial⟩
  | c :: rest, h => by
      have h1 : ∀ d ∈ rest, c.id ≤ d.id := h.1
      have h2 : SortedIds rest := h.2
      by_cases hb : b.id ≤ c.id
      · show SortedIds (insertById b (c :: rest))
        simp only [insertById, if_pos hb]
        refine ⟨?_, h⟩
        intro d hd
        rcases List.mem_cons.mp hd with hd | hd
        · subst hd; exact hb
        · exact Nat.le_trans hb (h1 d hd)
      · have hcb : c.id ≤ b.id := by omega
        show SortedIds (insertById b (c :: rest))
        simp only [insertById, if_neg hb]
        refine ⟨?_, insertById_sorted b rest h2⟩
        intro d hd
        rcases (mem_insertById b rest d).mp hd with hd | hd
        · subst hd; exact hcb
        · exact h1 d hd

theorem sortBlocks_sorted : ∀ l : List Block, SortedIds (sortBlocks l)
  | [] => trivial
  | b :: rest => insertById_sorted b (sortBlocks rest) (sortBlocks_sorted rest)

theorem canonWF_sorted {r : RawProgram} (h : CanonWF r) : SortedIds r.blocks := by
  have hb : sortBlocks r.blocks = r.blocks := congrArg RawProgram.blocks h
  rw [← hb]
  exact sortBlocks_sorted r.blocks

/-- **BREAK 4.** The target's `ProgramWF` entails that the entry block has the
minimum ID in the table. This is a consequence of the two substituted clauses
together, and it is a property `ALGEBRA.md` never states. -/
theorem programWF_forces_minimal_entry {rho : Env} {r : RawProgram}
    (h : ProgramWF rho r) : ∀ i ∈ blockIds r, r.entry ≤ i := by
  have hs : SortedIds r.blocks := canonWF_sorted h.2
  have he : (blockIds r).head? = some r.entry := h.1.2.2.2.2
  cases hbs : r.blocks with
  | nil =>
      intro i hi
      rw [blockIds, hbs] at hi
      simp at hi
  | cons b rest =>
      rw [blockIds, hbs] at he
      simp only [List.map_cons, List.head?_cons, Option.some.injEq] at he
      rw [hbs] at hs
      have hs1 : ∀ c ∈ rest, b.id ≤ c.id := hs.1
      intro i hi
      rw [blockIds, hbs] at hi
      simp only [List.map_cons, List.mem_cons] at hi
      rcases hi with hi | hi
      · omega
      · obtain ⟨c, hc, hci⟩ := List.mem_map.mp hi
        have := hs1 c hc
        omega

/-- The concrete cost. A two-block program, entry 5, jump 5 -> 1: well formed
on every clause `ALGEBRA.md:297-318` lists, and every clause the siblings
model. The target's checker refuses it in BOTH of its presentations, so no
`CheckedProgram` for it exists at any environment. -/
def fiveFirst : RawProgram :=
  { entry := 5, blocks := [⟨5, [], [], .jump 1⟩, ⟨1, [], [], .close⟩] }

def oneFirst : RawProgram :=
  { entry := 5, blocks := [⟨1, [], [], .close⟩, ⟨5, [], [], .jump 1⟩] }

theorem fiveFirst_refused : checkClauses demoEnv fiveFirst = .error .canon := rfl

theorem oneFirst_refused :
    checkClauses demoEnv oneFirst = .error (.entry 5 (some 1)) := rfl

theorem fiveFirst_not_wf : ¬ ProgramWF demoEnv fiveFirst := by
  intro h
  have := clauses_complete h
  rw [fiveFirst_refused] at this
  exact nomatch this

theorem oneFirst_not_wf : ¬ ProgramWF demoEnv oneFirst := by
  intro h
  have := clauses_complete h
  rw [oneFirst_refused] at this
  exact nomatch this

/-- Both presentations are well formed at the sibling clause set. So the target's
`check_complete` / `erase_readmitted` hold over a strictly smaller domain than
the packet's `ProgramWF`. -/
theorem fiveFirst_wf_at_sibling_clauses : ProgramWFcoreMem demoEnv fiveFirst :=
  ⟨(nodupB_iff _).mp rfl, (refsB_iff _).mp rfl, (linesB_iff _).mp rfl,
   (foreignB_iff _ _).mp rfl, by unfold EntryMem; decide⟩

theorem oneFirst_wf_at_sibling_clauses : ProgramWFcoreMem demoEnv oneFirst :=
  ⟨(nodupB_iff _).mp rfl, (refsB_iff _).mp rfl, (linesB_iff _).mp rfl,
   (foreignB_iff _ _).mp rfl, by unfold EntryMem; decide⟩

/-! ### The environment index is a modelling choice, not a spec defect

`T014.lean` finding (4) says `EC1-D021 ProgramWF : RawProgram -> Prop` is
"under-specified" because `ALGEBRA.md:312`'s `ForeignWF` needs a registry the
raw program does not carry. `T010.lean:271-281` carries one: `RawProgram` has a
`foreigns : List ForeignDecl` field, so `ForeignWF (r : RawProgram) : Prop`
(`T010.lean:639`) discharges the same clause at `EC1-D021`'s stated arity. The
shape below is that design in miniature; it type-checks at the DAG's arity, so
registry-relativity forces no index. -/

structure RawProgramR where
  entry : Nat
  blocks : List Block
  registry : List UInt8
  deriving DecidableEq

/-- `ForeignWF` at `EC1-D021`'s arity: one argument, no environment. -/
def ForeignWFclosed (r : RawProgramR) : Prop :=
  ∀ b ∈ r.blocks, ∀ f ∈ b.foreign, f ∈ r.registry

theorem foreignWFclosed_is_program_relative (r : RawProgramR) :
    ForeignWFclosed r ↔ ForeignWF ⟨r.registry⟩ ⟨r.entry, r.blocks⟩ := Iff.rfl

/-! ## §6 — non-degeneracy: the carrier is not empty above one block

The target's only positive witness `demoRaw` is a SINGLE block with no jumps,
so `RefsWF` is never exercised positively and `NoDupIds` is never exercised on
a two-element list positively. It is not a vacuity break — the carrier does
admit multi-block programs — but the file does not show it, so it is shown
here. -/

def twoBlockGood : RawProgram :=
  { entry := 0, blocks := [⟨0, [PLine.load (.ans 0)], [7], .jump 1⟩, ⟨1, [], [], .close⟩] }

theorem twoBlockGood_accepts : checkClauses demoEnv twoBlockGood = .ok () := rfl

def twoBlockChecked : CheckedProgram demoEnv (synthAER twoBlockGood) :=
  ⟨twoBlockGood, clauses_sound twoBlockGood_accepts, rfl⟩

theorem twoBlockGood_refsWF : RefsWF twoBlockGood :=
  (clauses_sound twoBlockGood_accepts).1.2.1

/-! ## §7 — the falsifier battery, at this carrier

`EC1-F02`, `F04`-`F09` have no carrier here (no `Resume`, region, handler,
fiber, resource or `AER` structure is modelled), so they are NOT exercised and
that is recorded, not glossed. -/

/-- `EC1-F01` — delete the target block. Rejected at the refs clause. -/
def f01_danglingJump : RawProgram :=
  { entry := 0, blocks := [⟨0, [], [], .jump 9⟩] }

theorem f01_rejected :
    checkClauses demoEnv f01_danglingJump = .error (.refs (some 9)) := rfl

theorem f01_not_wf : ¬ ProgramWF demoEnv f01_danglingJump := by
  intro h; have := clauses_complete h; rw [f01_rejected] at this; exact nomatch this

/-- `EC1-F03` — duplicate block ID. Rejected at the ids clause, strictly first
in the frozen order (`R16` part 2 / `EC1-CE030`). -/
def f03_dupIds : RawProgram :=
  { entry := 0, blocks := [⟨0, [], [], .close⟩, ⟨0, [], [], .close⟩] }

theorem f03_rejected : checkClauses demoEnv f03_dupIds = .error (.ids (some 0)) := rfl

theorem f03_not_wf : ¬ ProgramWF demoEnv f03_dupIds := by
  intro h; have := clauses_complete h; rw [f03_rejected] at this; exact nomatch this

/-- `EC1-F10` — normalize an already normalized graph. The target proves no
general idempotence (`EC1-T006` is an `EC1-S1` row it did not consume). At
these witnesses the fixed point holds by kernel reduction. -/
theorem f10_demo : normalizeRaw (normalizeRaw demoRaw) = normalizeRaw demoRaw := rfl
theorem f10_twoBlock :
    normalizeRaw (normalizeRaw twoBlockGood) = normalizeRaw twoBlockGood := rfl
theorem f10_badOrder :
    normalizeRaw (normalizeRaw badOrderRaw) = normalizeRaw badOrderRaw := rfl
theorem f10_dupIds : normalizeRaw (normalizeRaw f03_dupIds) = normalizeRaw f03_dupIds := rfl

/-- `EC1-F81` — one raw program, two independent defects, and the LATER
diagnostic demanded. This MUST stay red. Here a bad line (clause 3) and an
unregistered foreign ID (clause 4) coexist; the checker returns the earlier
clause, and the accumulating reading is refuted by kernel computation. -/
def f81_twoDefects : RawProgram :=
  { entry := 0, blocks := [⟨0, [PLine.load (.ans 4294967296)], [9], .close⟩] }

theorem f81_returns_the_first :
    checkClauses demoEnv f81_twoDefects = .error (.lines (some 0)) := rfl

theorem f81_stays_red :
    ∀ f : Option UInt8, checkClauses demoEnv f81_twoDefects ≠ .error (.foreign f) := by
  intro f h
  rw [f81_returns_the_first] at h
  exact nomatch h

/-- Both clauses genuinely condemn it, which is what makes `F81` a real
falsifier rather than a missing defect. -/
theorem f81_both_clauses_condemn :
    linesB f81_twoDefects = false ∧ foreignB demoEnv f81_twoDefects = false :=
  ⟨rfl, rfl⟩

/-! ## §8 — what still stands

The target's row-as-written, its restatement, and its `T013` strengthening are
all reproduced here unchanged and remain true AT ITS OWN CARRIER. The break is
not that these fail; it is that the carrier is not the packet's. -/

theorem target_erase_wf_still_holds {rho : Env} {aer : AER} (p : CheckedProgram rho aer) :
    ProgramWF rho (erase p) := p.wf

theorem target_erase_wf_is_still_the_field :
    @target_erase_wf_still_holds = fun _ _ p => CheckedProgram.wf p := rfl

end AttackT014

/-! ## Kernel receipts -/

#print axioms AttackT014.fidelity_badOrder_core
#print axioms AttackT014.fidelity_badOrder_normalized_entryB_false
#print axioms AttackT014.fidelity_badOrder_refused
#print axioms AttackT014.fidelity_badLine_rejected
#print axioms AttackT014.fidelity_badForeign_rejected
#print axioms AttackT014.mem_insertById
#print axioms AttackT014.insertById_perm
#print axioms AttackT014.sortBlocks_perm
#print axioms AttackT014.normalizeRaw_perm
#print axioms AttackT014.blockIds_perm
#print axioms AttackT014.noDupIds_iff_nodup

-- BREAK 1
#print axioms AttackT014.normalizer_preserves_wf_at_the_sibling_entry_clause
#print axioms AttackT014.erase_wf_designB_holds_at_the_sibling_entry_clause
#print axioms AttackT014.badOrder_core_mem
#print axioms AttackT014.badOrder_survives_normalization
#print axioms AttackT014.badOrder_normalized_fails_only_the_positional_clause

-- BREAK 2
#print axioms AttackT014.badOrder_satisfies_packet_clause12
#print axioms AttackT014.badOrder_entry_lookup_survives
#print axioms AttackT014.badOrder_fails_target_clause12

-- BREAK 3
#print axioms AttackT014.erase_wfC
#print axioms AttackT014.erase_wfC_needs_soundness
#print axioms AttackT014.foreignWFclosed_is_program_relative

-- BREAK 4
#print axioms AttackT014.insertById_sorted
#print axioms AttackT014.sortBlocks_sorted
#print axioms AttackT014.canonWF_sorted
#print axioms AttackT014.programWF_forces_minimal_entry
#print axioms AttackT014.fiveFirst_refused
#print axioms AttackT014.oneFirst_refused
#print axioms AttackT014.fiveFirst_not_wf
#print axioms AttackT014.oneFirst_not_wf
#print axioms AttackT014.fiveFirst_wf_at_sibling_clauses
#print axioms AttackT014.oneFirst_wf_at_sibling_clauses

-- non-degeneracy
#print axioms AttackT014.twoBlockGood_accepts
#print axioms AttackT014.twoBlockGood_refsWF

-- falsifiers
#print axioms AttackT014.f01_rejected
#print axioms AttackT014.f01_not_wf
#print axioms AttackT014.f03_rejected
#print axioms AttackT014.f03_not_wf
#print axioms AttackT014.f10_demo
#print axioms AttackT014.f10_twoBlock
#print axioms AttackT014.f10_badOrder
#print axioms AttackT014.f10_dupIds
#print axioms AttackT014.f81_returns_the_first
#print axioms AttackT014.f81_stays_red
#print axioms AttackT014.f81_both_clauses_condemn

-- what stands
#print axioms AttackT014.target_erase_wf_still_holds
#print axioms AttackT014.target_erase_wf_is_still_the_field
