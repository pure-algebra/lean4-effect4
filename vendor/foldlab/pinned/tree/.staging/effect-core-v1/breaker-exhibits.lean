import Cas.Lang.Wp
import Cas.Lang.Tower

/-!
# Effect Core v1 — the breaker's adversarial record

## What this file IS

An ADVERSARIAL RECORD against `.staging/effect-core-v1/workshop/exhibits.lean`
(15 theorems, read at 2026-08-31 07:30) and the packet sections it decides:
`ALGEBRA.md` §10 and §12, `PROOF-DAG.md` §6 and §12, `CONTRACT-PACKET.md`.
Written 2026-08-31, Lean `leanprover/lean4:v4.33.1`.

Every declaration below is an ATTACK: either a witness that a claim is weaker
than advertised, or a break attempt that FAILED and is kept because a failed
break is earned confidence and earned confidence is record. Prose objections
were not admitted; what is here is what elaborated.

Stage: `lean-assurance-review` (`.claude/skills/lean/workflows/`), its
"try to refute each link" section. Its first standing rule binds this file as
much as the one it attacks: **a successful elaboration proves the stated
proposition only.** Fifty-nine propositions hold below, forty of them receipted
at the foot. Nothing more.

## What this file is NOT

It is NOT part of any Lake target and MUST NOT become one. It adds no
definition to `Cas`, moves no bytes, touches no ledger, and mutates nothing in
the reviewed tree.

## Fences (the `contracts/attacks/PDD-N/Attack.lean` house form)

- outside every lake target;
- elaborated by `lake env lean` from `library/cas`;
- no `sorry`, no `native_decide`, no `Classical.choice`;
- digests in `#eval` only — every address function here is a toy
  (`Falsifier.lenAddr`, and a constant `constH`), and no `#guard` or kernel
  `decide` computes a digest.

## How to elaborate it

From `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/breaker-exhibits.lean
```

Expected: elaborates clean, no errors, no warnings. Every `#guard` is a
compile-time assertion — a red `#guard` IS a finding. The `#print axioms` block
at the foot is read, not asserted; every line must show `[propext]` or
`[propext, Quot.sound]`.

## The verdicts

| § | Claim under attack | Verdict |
|---|---|---|
| 1 | `inject_embed` / `runCore_runP` at degenerate tables | SURVIVES |
| 1.4 | `project_inject` — `toPProg` as `projectCas` | **BROKEN** |
| 2 | `coherent` / `coherent_le` / `denotes_unique` | SURVIVES, narrowed |
| 3 | `exhausted_is_not_a_refusal` | NARROWED |
| 4 | `Scoped`: "scoped bodies need no new handler type" | **BROKEN** |
| 5 | `wlp` as EffHOL's modality, (Mod-E) | NARROWED |
| 6 | `classifier_finer_than_semantics` (the new §8) | SURVIVES, narrowed |

Read against `workshop/exhibits.lean` at 27629 bytes / sha256 `b31284930eb903ab…`
(653 lines, 17 receipted theorems), `PROOF-DAG.md` at 42519 bytes, `ALGEBRA.md`
at 41028 bytes, `CONTRACT-PACKET.md` at 48033 bytes, `COUNTEREXAMPLES.md` at
15131 bytes. The exhibits file grew twice during this run; the §0 carrier was
re-verified byte-identical against the final read.

The graph carrier in §0 is copied VERBATIM from `workshop/exhibits.lean` §2–§5
and §6 (the file is not a library module, so it cannot be imported). Any
divergence would void the attack, so nothing here is "improved".
-/
namespace EffectCoreBreaker

open Cas.Lang
open Cas (Bytes Addr32 Node Word Binding Ref)

/-! ## §0 — the carrier under attack, verbatim -/

abbrev BlockId := Nat

inductive GTerm where
  | ret
  | jump (b : BlockId)
  | brTag (src : PIn) (tag : UInt8) (t f : BlockId)
  deriving DecidableEq

structure GBlock where
  body : PProg
  term : GTerm
  deriving DecidableEq

structure GProg where
  blocks : List GBlock
  entry  : BlockId
  deriving DecidableEq

def blockBody (g : GProg) (rec : BlockId → List Addr32 → Prog CasSig Addr32)
    (b : BlockId) (env : List Addr32) : Prog CasSig Addr32 :=
  match g.blocks[b]? with
  | none => failWith "graph: no such block"
  | some blk =>
    (embedFrom env blk.body).bind fun a =>
      let env' := env ++ [a]
      match blk.term with
      | .ret => .pure a
      | .jump b' => rec b' env'
      | .brTag src tag t f =>
        match src.resolve env' with
        | none => failWith "graph: dangling scrutinee"
        | some x =>
          (load x).bind fun n => rec (if n.tag == tag then t else f) env'

def runBlocks (g : GProg) : Nat → BlockId → List Addr32 → Prog CasSig Addr32
  | 0, _, _ => failWith "graph: fuel exhausted"
  | fuel + 1, b, env => blockBody g (runBlocks g fuel) b env

def denoteG (g : GProg) (fuel : Nat) : Prog CasSig Addr32 :=
  runBlocks g fuel g.entry []

def ofPProg (p : PProg) : GProg := ⟨[⟨p, .ret⟩], 0⟩

def toPProg (g : GProg) : Option PProg :=
  match g.blocks, g.entry with
  | [⟨p, .ret⟩], 0 => some p
  | _, _ => none

theorem inject_embed (p : PProg) (fuel : Nat) :
    denoteG (ofPProg p) (fuel + 1) = embed p :=
  Prog.bind_pure_right (embedFrom [] p)

theorem runCore_runP (H : Bytes → Addr32) (p : PProg) (w : Word) :
    run H (p.length + 1) (denoteG (ofPProg p) 1) w = runP H p w := by
  rw [inject_embed p 0]
  exact runP_embed_agree H p w

/-! ### Fixtures -/

def zeroAddr : Addr32 := Falsifier.zeroAddr
def oneAddr  : Addr32 := ⟨List.replicate 32 1, by simp⟩

/-- The node `Falsifier.putA` admits: no payload, no references. -/
def nA : Node := ⟨0, 0, [], []⟩
/-- A DIFFERENT operand-free node — same shape, other kind tag. -/
def nB : Node := ⟨0, 1, [], []⟩

theorem ok_ne_error {α β : Type} (x : α) (e : β) :
    (Except.ok x : Except β α) ≠ .error e := by simp

theorem nA_ne_nB : nA ≠ nB := by decide
theorem zero_ne_one : zeroAddr ≠ oneAddr := by decide

/-! ## §1 — `inject_embed` / `runCore_runP` under degenerate tables

`runCore_runP` is stated `∀ p`, and its proof is `inject_embed` followed by
`runP_embed_agree`, which is itself `∀ p`. Nothing in either proof inspects the
table. The three degenerate shapes therefore cannot break it, and the exhibits
below say what each one AGREES ON — which is the part worth recording, because
in two of the three cases the agreed value is a REFUSAL. -/

/-- The empty table. Both sides refuse with `defun: empty program`; the
one-block graph inherits the refusal rather than answering. -/
theorem empty_table_survives (H : Bytes → Addr32) :
    run H (([] : PProg).length + 1) (denoteG (ofPProg []) 1) []
        = runP H ([] : PProg) []
      ∧ runP H ([] : PProg) []
        = (Status.refused (.failed "defun: empty program"), []) :=
  ⟨runCore_runP H [] [], rfl⟩

/-- A table whose LAST line is a `load`. The load answers its own source
address into the history, so the graph answers it too — at a word that holds
the address. -/
def loadLast : PProg := [.load (.lit zeroAddr)]

theorem load_last_survives_present (H : Bytes → Addr32) :
    run H (loadLast.length + 1) (denoteG (ofPProg loadLast) 1)
          [Binding.mk zeroAddr nA]
        = runP H loadLast [Binding.mk zeroAddr nA]
      ∧ runP H loadLast [Binding.mk zeroAddr nA]
        = (Status.done zeroAddr, [Binding.mk zeroAddr nA]) :=
  ⟨runCore_runP H loadLast _, rfl⟩

theorem load_last_survives_absent (H : Bytes → Addr32) :
    run H (loadLast.length + 1) (denoteG (ofPProg loadLast) 1) []
        = runP H loadLast []
      ∧ runP H loadLast [] = (Status.refused (.noObject zeroAddr), []) :=
  ⟨runCore_runP H loadLast [], rfl⟩

/-- A table with a DANGLING answer index. -/
def danglingAns : PProg := [.put 0 0 [] [(0, .ans 5)]]

theorem dangling_ans_survives (H : Bytes → Addr32) :
    run H (danglingAns.length + 1) (denoteG (ofPProg danglingAns) 1) []
        = runP H danglingAns []
      ∧ runP H danglingAns []
        = (Status.refused (.failed "defun: dangling answer index"), []) :=
  ⟨runCore_runP H danglingAns [], rfl⟩

/-! ### §1.4 — **BROKEN**: `toPProg` is not `projectCas`

`project_inject` proves `toPProg (ofPProg p) = some p`. That makes `toPProg` a
left inverse of `ofPProg` ON THE IMAGE OF `ofPProg`, which is a weaker claim
than the packet's `projectCas`: a projection out of the CAS-only FRAGMENT.

`toPProg` matches one literal normal form — a one-element block list whose sole
block terminates `.ret`, at entry `0`. Every other CAS-only graph, no matter
what it denotes, is refused. The three witnesses below are all CAS-only (every
terminator is `.ret`, no `jump`, no `brTag`, so no cycle and no branch), all
denote EXACTLY `embed p`, and none of them projects. -/

/-- CAS-only, entry `0`, one reachable block — with an unreachable second
block. The shape any dead-code pass leaves behind. -/
def unreachableTail (p : PProg) : GProg := ⟨[⟨p, .ret⟩, ⟨p, .ret⟩], 0⟩

/-- CAS-only, one reachable block, entry `1`. The shape any block relabelling
leaves behind. -/
def entryNotZero (p : PProg) : GProg := ⟨[⟨[], .ret⟩, ⟨p, .ret⟩], 1⟩

theorem unreachableTail_denotes (p : PProg) (fuel : Nat) :
    denoteG (unreachableTail p) (fuel + 1) = embed p :=
  Prog.bind_pure_right (embedFrom [] p)

theorem entryNotZero_denotes (p : PProg) (fuel : Nat) :
    denoteG (entryNotZero p) (fuel + 1) = embed p :=
  Prog.bind_pure_right (embedFrom [] p)

theorem toPProg_blind_to_unreachableTail (p : PProg) :
    toPProg (unreachableTail p) = none := rfl

theorem toPProg_blind_to_entryNotZero (p : PProg) :
    toPProg (entryNotZero p) = none := rfl

/-- **THE COUNTEREXAMPLE.** `toPProg` is not a function of the denotation: two
graphs with the SAME `Prog` at every positive fuel, one projected, one refused.
A projection out of a fragment must at least be defined on the fragment; this
one is defined on a normal form. -/
theorem toPProg_is_not_semantic :
    ∃ (g g' : GProg) (p : PProg),
      (∀ fuel, denoteG g (fuel + 1) = denoteG g' (fuel + 1))
        ∧ toPProg g' = some p
        ∧ toPProg g = none := by
  refine ⟨unreachableTail Falsifier.onePut, ofPProg Falsifier.onePut,
    Falsifier.onePut, fun fuel => ?_, rfl, rfl⟩
  rw [unreachableTail_denotes, inject_embed]

/-- The same at the other end: `toPProg` refuses a graph whose only difference
from the accepted normal form is which index the entry carries. -/
theorem toPProg_is_not_entry_stable :
    ∃ (g g' : GProg) (p : PProg),
      (∀ fuel, denoteG g (fuel + 1) = denoteG g' (fuel + 1))
        ∧ toPProg g' = some p
        ∧ toPProg g = none := by
  refine ⟨entryNotZero Falsifier.onePut, ofPProg Falsifier.onePut,
    Falsifier.onePut, fun fuel => ?_, rfl, rfl⟩
  rw [entryNotZero_denotes, inject_embed]

/-- The SOUND half, for the record: when `toPProg` does answer, it answers
right — the accepted normal form denotes what it projects to. So the defect is
incompleteness, not unsoundness, and the repair is a real projection (walk the
reachable `.ret`-only subgraph from `entry`), not a different theorem. -/
theorem toPProg_sound (g : GProg) (p : PProg) (fuel : Nat)
    (h : toPProg g = some p) : denoteG g (fuel + 1) = embed p := by
  obtain ⟨blocks, entry⟩ := g
  match blocks with
  | [] =>
      have hn : toPProg (⟨[], entry⟩ : GProg) = none := by cases entry <;> rfl
      rw [hn] at h; simp at h
  | ⟨body, .jump b⟩ :: tail =>
      have hn : toPProg (⟨⟨body, .jump b⟩ :: tail, entry⟩ : GProg) = none := by
        cases entry <;> rfl
      rw [hn] at h; simp at h
  | ⟨body, .brTag s t u v⟩ :: tail =>
      have hn : toPProg (⟨⟨body, .brTag s t u v⟩ :: tail, entry⟩ : GProg) = none := by
        cases entry <;> rfl
      rw [hn] at h; simp at h
  | ⟨body, .ret⟩ :: blk :: tail =>
      have hn : toPProg (⟨⟨body, .ret⟩ :: blk :: tail, entry⟩ : GProg) = none := by
        cases entry <;> rfl
      rw [hn] at h; simp at h
  | [⟨body, .ret⟩] =>
      match entry, h with
      | 0, h =>
        have hb : body = p := Option.some.inj h
        subst hb
        exact Prog.bind_pure_right (embedFrom [] body)
      | n + 1, h =>
        have hn : toPProg (⟨[⟨body, .ret⟩], n + 1⟩ : GProg) = none := rfl
        rw [hn] at h; simp at h


/-! ## §2 — `coherent` / `coherent_le` / `denotes_unique`

The three attacks the brief names — out-of-range block lookup MID-RUN, a `load`
of an answer index that only exists once an earlier block has run, and two fuels
answering differently — are all answered by ONE theorem, and it is STRONGER
than the exhibit's `coherent`.

The exhibit quantifies coherence over `.ok` outcomes only (`Refines`). That is
weaker than it needs to be: everything except the fuel-exhausted leaf is stable,
refusals included. Proving the stronger statement costs the same single
induction, settles §2 outright, and hands §3 its boundary for free. -/

section Coherence
variable (H : Bytes → Addr32)

/-- The big-step bind law, as in the exhibit. -/
theorem interpretRef_bind {A B} (p : Prog CasSig A) (f : A → Prog CasSig B)
    (w : Word) :
    interpretRef H (p.bind f) w
      = match interpretRef H p w with
        | .ok (a, w₁) => interpretRef H (f a) w₁
        | .error e => .error e := by
  have hw := congrArg (fun m => m w) (interpret_bind (referenceHandler H) p f)
  simp only [interpretRef]
  rw [hw]
  cases hp : interpret (referenceHandler H) p w with
  | ok aw =>
    obtain ⟨a, w₁⟩ := aw
    simp [bind, StateT.bind, Except.bind, hp]
  | error e => simp [bind, StateT.bind, Except.bind, hp]

/-- The out-of-fuel leaf, named once. -/
def exhausted : Refusal := .failed "graph: fuel exhausted"

/-- **STABILITY** — the strengthening. At every state whose outcome is not the
exhausted leaf, the recursive tail may be replaced without changing the outcome
AT ALL: same answer, same word, same refusal. -/
def Stable (rec rec' : BlockId → List Addr32 → Prog CasSig Addr32) : Prop :=
  ∀ b env w, interpretRef H (rec b env) w ≠ .error exhausted →
    interpretRef H (rec' b env) w = interpretRef H (rec b env) w

theorem blockBody_stable (g : GProg)
    {rec rec' : BlockId → List Addr32 → Prog CasSig Addr32}
    (hr : Stable H rec rec') :
    Stable H (blockBody g rec) (blockBody g rec') := by
  intro b env w h
  unfold blockBody at h ⊢
  cases hb : g.blocks[b]? with
  | none => rfl
  | some blk =>
    rw [hb] at h
    dsimp only at h ⊢
    simp only [interpretRef_bind] at h ⊢
    cases hbody : interpretRef H (embedFrom env blk.body) w with
    | error e => rfl
    | ok aw =>
      obtain ⟨a₀, w₀⟩ := aw
      rw [hbody] at h
      dsimp only at h ⊢
      cases hterm : blk.term with
      | ret => rfl
      | jump b' =>
        rw [hterm] at h
        exact hr b' _ w₀ h
      | brTag src tag t f =>
        rw [hterm] at h
        dsimp only at h ⊢
        cases hs : src.resolve (env ++ [a₀]) with
        | none => rfl
        | some x =>
          rw [hs] at h
          dsimp only at h ⊢
          simp only [interpretRef_bind] at h ⊢
          cases hl : interpretRef H (load x) w₀ with
          | error e => rfl
          | ok nw =>
            obtain ⟨nd, w₁⟩ := nw
            rw [hl] at h
            dsimp only at h ⊢
            exact hr _ _ w₁ h

/-- Fuel `0` decides EVERY state the same way — the leaf carries no information
about the graph. -/
theorem runBlocks_zero (g : GProg) (b : BlockId) (env : List Addr32) (w : Word) :
    interpretRef H (runBlocks g 0 b env) w = .error exhausted := rfl

theorem stable_succ : ∀ (n : Nat) (g : GProg),
    Stable H (runBlocks g n) (runBlocks g (n + 1))
  | 0, g => fun b env w h => absurd (runBlocks_zero H g b env w) h
  | n + 1, g => blockBody_stable H g (stable_succ n g)

theorem stable_le : ∀ (m n : Nat) (g : GProg), n ≤ m →
    Stable H (runBlocks g n) (runBlocks g m)
  | 0, n, _, hle => by
    have hz : n = 0 := Nat.le_zero.mp hle
    subst hz; exact fun _ _ _ _ => rfl
  | m + 1, n, g, hle => by
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · have ih := stable_le m n g (Nat.le_of_lt_succ hlt)
      intro b env w h
      have e1 := ih b env w h
      have h' : interpretRef H (runBlocks g m b env) w ≠ .error exhausted := by
        rw [e1]; exact h
      have e2 := stable_succ H m g b env w h'
      rw [e2, e1]
    · have hz : n = m + 1 := Nat.le_antisymm hle hge
      subst hz; exact fun _ _ _ _ => rfl

/-- The exhibit's `coherent`, recovered as a corollary of the stronger law. -/
theorem coherent (n : Nat) (g : GProg) (b : BlockId) (env : List Addr32)
    (w : Word) (a : Addr32) (w' : Word)
    (h : interpretRef H (runBlocks g n b env) w = .ok (a, w')) :
    interpretRef H (runBlocks g (n + 1) b env) w = .ok (a, w') := by
  rw [stable_succ H n g b env w (by rw [h]; exact ok_ne_error _ _), h]

def Denotes (g : GProg) (w : Word) (a : Addr32) (w' : Word) : Prop :=
  ∃ n, interpretRef H (denoteG g n) w = .ok (a, w')

/-- `denotes_unique`, re-proved through stability. It SURVIVES: two witnessing
fuels agree, whatever the graph does with block indices or answer indices. -/
theorem denotes_unique (g : GProg) (w : Word) (a₁ a₂ : Addr32) (w₁ w₂ : Word)
    (h₁ : Denotes H g w a₁ w₁) (h₂ : Denotes H g w a₂ w₂) :
    a₁ = a₂ ∧ w₁ = w₂ := by
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₂, hn₂⟩ := h₂
  simp only [denoteG] at hn₁ hn₂
  have k₁ := stable_le H (max n₁ n₂) n₁ g (Nat.le_max_left _ _) g.entry [] w
    (by rw [hn₁]; exact ok_ne_error _ _)
  have k₂ := stable_le H (max n₁ n₂) n₂ g (Nat.le_max_right _ _) g.entry [] w
    (by rw [hn₂]; exact ok_ne_error _ _)
  rw [hn₁] at k₁
  rw [hn₂] at k₂
  have h2 : (a₁, w₁) = (a₂, w₂) := Except.ok.inj (k₁.symm.trans k₂)
  exact ⟨(Prod.mk.inj h2).1, (Prod.mk.inj h2).2⟩

end Coherence

/-! ### §2's three named attacks, as witnesses -/

/-- A word holding `zeroAddr`. Every fact below is `H`-independent because
`load` never consults the address function. -/
def wZ : Word := [Binding.mk zeroAddr nA]

/-- A block body that answers at `wZ` for every `H`. -/
def okBody : PProg := [.load (.lit zeroAddr)]

/-- ATTACK 2a: the block index goes OUT OF RANGE mid-run — after block `0` has
already succeeded. -/
def offEndGraph : GProg := ⟨[⟨okBody, .jump 7⟩], 0⟩

theorem offEnd_fuel1 (H : Bytes → Addr32) :
    interpretRef H (denoteG offEndGraph 1) wZ = .error exhausted := rfl

theorem offEnd_fuel_ge2 (H : Bytes → Addr32) (n : Nat) :
    interpretRef H (denoteG offEndGraph (n + 2)) wZ
      = .error (.failed "graph: no such block") := rfl

/-- The out-of-range graph DENOTES nothing — `Denotes` is empty, so
`denotes_unique` is not even reached. -/
theorem offEnd_never_denotes (H : Bytes → Addr32) (a : Addr32) (w' : Word) :
    ¬ Denotes H offEndGraph wZ a w' := by
  rintro ⟨n, hn⟩
  match n with
  | 0 => exact ok_ne_error _ _ (hn.symm.trans rfl)
  | 1 => rw [offEnd_fuel1] at hn; exact ok_ne_error _ _ hn.symm
  | k + 2 => rw [offEnd_fuel_ge2] at hn; exact ok_ne_error _ _ hn.symm

/-- ATTACK 2b: a block body whose `load` names an answer index that exists only
because an EARLIER BLOCK ran. `ans 0` in block `1` resolves against the history
block `0` contributed. The answer is the same at every sufficient fuel — the
history a block sees is fixed by the PATH, never by the fuel. -/
def chainGraph : GProg :=
  ⟨[⟨okBody, .jump 1⟩, ⟨[.load (.ans 0)], .ret⟩], 0⟩

theorem chain_fuel1 (H : Bytes → Addr32) :
    interpretRef H (denoteG chainGraph 1) wZ = .error exhausted := rfl

theorem chain_stable_from_2 (H : Bytes → Addr32) (n : Nat) :
    interpretRef H (denoteG chainGraph (n + 2)) wZ = .ok (zeroAddr, wZ) := rfl

/-- ATTACK 2c, refuted: no two fuels give different `.ok` answers. -/
theorem no_two_fuels_disagree (H : Bytes → Addr32) (g : GProg) (w : Word)
    (m n : Nat) (a₁ a₂ : Addr32) (w₁ w₂ : Word)
    (h₁ : interpretRef H (denoteG g n) w = .ok (a₁, w₁))
    (h₂ : interpretRef H (denoteG g m) w = .ok (a₂, w₂)) :
    a₁ = a₂ ∧ w₁ = w₂ :=
  denotes_unique H g w a₁ a₂ w₁ w₂ ⟨n, h₁⟩ ⟨m, h₂⟩

/-- **THE NARROWING of §2.** What the family determines is the ANSWER, not the
outcome: the REFUSAL is not a function of the graph. Two fuels, two different
refusals, at every `H`. `Denotes` is a partial function; "the graph's meaning"
in the refusing direction is not defined by the colimit at all. -/
theorem denotes_does_not_determine_the_refusal :
    ∃ (g : GProg) (w : Word) (m n : Nat) (r₁ r₂ : Refusal),
      r₁ ≠ r₂
        ∧ ∀ H : Bytes → Addr32,
            interpretRef H (denoteG g n) w = .error r₁
              ∧ interpretRef H (denoteG g m) w = .error r₂ := by
  refine ⟨offEndGraph, wZ, 2, 1, exhausted, .failed "graph: no such block",
    ?_, fun H => ⟨offEnd_fuel1 H, offEnd_fuel_ge2 H 0⟩⟩
  intro hc
  exact absurd (Refusal.failed.inj hc) (by decide)

/-! ## §3 — `exhausted_is_not_a_refusal`: NARROWED

The exhibit's theorem is true, and its two conjuncts are true of `onePutGraph`.
It is NOT a schema: the second conjunct is vacuous for a graph that has not
halted by fuel 1, and that is most graphs with a cycle. What survives, and what
the packet should carry instead, is the boundary theorem below. -/

/-- The vacuity witness: a graph whose block jumps to ITSELF. Fuel 0, fuel 1 and
fuel 2 all report the SAME refusal — the exhausted leaf — so the exhibit's
"at fuel 1 it cannot report that refusal" is false of this graph. -/
def loopGraph : GProg := ⟨[⟨okBody, .jump 0⟩], 0⟩

theorem loop_exhausts_at_0_1_2 (H : Bytes → Addr32) :
    interpretRef H (denoteG loopGraph 0) wZ = .error exhausted
      ∧ interpretRef H (denoteG loopGraph 1) wZ = .error exhausted
      ∧ interpretRef H (denoteG loopGraph 2) wZ = .error exhausted :=
  ⟨rfl, rfl, rfl⟩

/-- The same at the exhibit's own `run` face, so the comparison is like for
like: at fuel 0 AND at fuel 1 the loop graph refuses with the exhausted
reason, which is exactly what `exhausted_is_not_a_refusal` asserts cannot
happen for `onePutGraph`. -/
theorem loop_run_exhausts (H : Bytes → Addr32) :
    run H 4 (denoteG loopGraph 0) wZ = (.refused exhausted, wZ)
      ∧ run H 4 (denoteG loopGraph 1) wZ = (.refused exhausted, wZ) :=
  ⟨rfl, rfl⟩

/-- **THE BOUNDARY, stated exactly.** Conflating `live` with `halt` is harmless
precisely on the outcomes that are not the exhausted leaf: every such outcome —
answer or refusal — is INVARIANT under increasing fuel. -/
theorem exhausted_is_the_only_unstable_leaf (H : Bytes → Addr32) (g : GProg)
    (w : Word) (m n : Nat) (hnm : n ≤ m)
    (h : interpretRef H (denoteG g n) w ≠ .error exhausted) :
    interpretRef H (denoteG g m) w = interpretRef H (denoteG g n) w :=
  stable_le H m n g hnm g.entry [] w h

/-- The other side of the boundary: at fuel `0` every graph, every word and
every `H` report the exhausted leaf, so that outcome distinguishes nothing.
This is why the leaf must be distinguished in the TYPE and not by its string. -/
theorem fuel_zero_is_contentless (H : Bytes → Addr32) (g : GProg) (w : Word) :
    interpretRef H (denoteG g 0) w = .error exhausted := rfl

/-- And the leaf really is unstable, so the boundary is sharp in both
directions. -/
theorem exhausted_leaf_is_unstable :
    ∃ (g : GProg) (w : Word), ∀ H : Bytes → Addr32,
      interpretRef H (denoteG g 1) w = .error exhausted
        ∧ interpretRef H (denoteG g 2) w ≠ .error exhausted := by
  refine ⟨offEndGraph, wZ, fun H => ⟨offEnd_fuel1 H, ?_⟩⟩
  rw [offEnd_fuel_ge2 H 0]
  intro hc
  exact absurd (Refusal.failed.inj (Except.error.inj hc)) (by decide)

/-! ### §4.3 — the two children, as ordinary block denotations

The counterexample of §4.2 is not about exotic programs: both children are
one-line blocks of the graph below, at fuel 1. -/

def catchGraph : GProg :=
  ⟨[⟨[.load (.lit zeroAddr)], .ret⟩, ⟨[.put 0 1 [] []], .ret⟩], 0⟩

/-! ## §4 — the `Scoped` section: **BROKEN** in its load-bearing half

`exhibits.lean` §6 claims scoped and higher-order operations need "no new
handler type", and typechecks a `Handler ScopeSig (ReaderT Env (Prog CasSig))`
to prove it. The `catchE` clause of that handler DISCARDS its handler block:

```
| .catchE body _hnd  => fun (g, fuel) => runBlocks g fuel body []
```

so the section's own witness never catches anything. This part asks whether
that is an oversight or an obstruction. It is an obstruction. -/

namespace Scoped

inductive ScopeE where
  | catchE   (body handler : BlockId)
  | ensuring (body finalizer : BlockId)
  | scoped   (body : BlockId)
  | provide  (key : Addr32) (body : BlockId)
  | raise    (err : Addr32)

abbrev ScopeE.Ans : ScopeE → Type
  | .catchE _ _   => Addr32
  | .ensuring _ _ => Addr32
  | .scoped _     => Addr32
  | .provide _ _  => Addr32
  | .raise _      => Empty

def ScopeSig : Sig := ⟨ScopeE, ScopeE.Ans⟩
def ScopedCasSig : Sig := CasSig ⊕ₛ ScopeSig

abbrev Env := GProg × Nat
abbrev ScopeM := ReaderT Env (Prog CasSig)

/-- The exhibit's handler, verbatim. -/
def scopeHandler : Handler ScopeSig ScopeM where
  handle
    | .catchE body _hnd  => fun (g, fuel) => runBlocks g fuel body []
    | .ensuring body fin => fun (g, fuel) =>
        (runBlocks g fuel body []).bind fun a =>
          (runBlocks g fuel fin []).bind fun _ => .pure a
    | .scoped body       => fun (g, fuel) => runBlocks g fuel body []
    | .provide _key body => fun (g, fuel) => runBlocks g fuel body []
    | .raise _err        => fun _ => failWith "scope: raised"

/-! ### §4.1 — the structural half: scoping is exactly ONE level deep

Every child of a scoped operation is a `BlockId` into a `GProg`, and a `GBlock`
body is a `PProg` — a table of `put` and `load` lines. There is no constructor
by which a block can perform a scoped operation. So the type below is not a
convenience: it is the whole expressive ceiling. A scoped op's meaning is a
STORE program, therefore `catchE`'s body cannot raise, cannot be `ensuring`,
and cannot be another `catchE`. Nesting is not a missing clause; it is
inexpressible. -/
example (op : ScopeSig.Op) (e : Env) : Prog CasSig (ScopeSig.Ans op) :=
  scopeHandler.handle op e

/-! ### §4.2 — the semantic half: no clause into `ReaderT Env (Prog CasSig)`
can catch

A `Handler ScopeSig ScopeM` clause for `.catchE b h` is exactly a function
`Env → BlockId → BlockId → Prog CasSig Addr32`. `ScopeCatchLaw` is what such a
clause must satisfy for the operation to deserve its name, stated against the
estate's own reference semantics. It is unsatisfiable. -/

def ScopeCatchLaw (k : Env → BlockId → BlockId → Prog CasSig Addr32) : Prop :=
  ∀ (H : Bytes → Addr32) (e : Env) (b h : BlockId) (w : Word),
    interpretRef H (k e b h) w
      = match interpretRef H (runBlocks e.1 e.2 b []) w with
        | .ok r => .ok r
        | .error _ => interpretRef H (runBlocks e.1 e.2 h []) w

/-- The address function of the counterexample: constant, so every node
addresses to `zeroAddr`. Level 0 — the estate assumes nothing about `H`
anywhere, and `Address.lean` exhibits exactly this degenerate function. -/
def constH : Bytes → Addr32 := fun _ => zeroAddr

/-- The two children. `probe` loads `zeroAddr`: it REFUSES at the empty word
and ANSWERS at `wZ`, and it changes no word either way — so the counterexample
does not turn on whether a catch rolls the word back. `hndB` puts the OTHER
node. Both are ordinary block denotations (§4.3). -/
def probe : Prog CasSig Addr32 := .vis (.load zeroAddr) (fun _ => .pure zeroAddr)
def hndB  : Prog CasSig Addr32 := .vis (.put nB) (fun a => .pure a)

theorem probe_refuses_at_nil :
    interpretRef constH probe [] = .error (.noObject zeroAddr) := rfl

theorem probe_answers_at_wZ :
    interpretRef constH probe wZ = .ok (zeroAddr, wZ) := rfl

theorem hndB_at_nil :
    interpretRef constH hndB [] = .ok (zeroAddr, [Binding.mk zeroAddr nB]) := rfl

/-- Both children ARE block denotations of `catchGraph` at fuel 1 — by `rfl`,
so the counterexample lives entirely inside the packet's own carrier. -/
theorem catchGraph_body : runBlocks catchGraph 1 0 [] = probe := rfl
theorem catchGraph_hnd  : runBlocks catchGraph 1 1 [] = hndB := rfl

/-- **THE SEPARATION LEMMA.** No store program answers `.ok` at BOTH the empty
word (leaving `[⟨zeroAddr, nB⟩]`) and at `wZ` (leaving `wZ`). The proof is one
case split, no induction: at the empty word the only operation that can succeed
is a fresh put, that put addresses to `zeroAddr` under `constH`, and at `wZ`
that same put either CONFLICTS — refusing, which the second hypothesis forbids
— or DUPLICATES, which makes the two words coincide and the two runs the same
run from there. A store program cannot test for absence: `load` of an absent
address is itself a refusal, and a put's answer is a function of the node, not
of the word. -/
theorem constH_no_separator (c : Prog CasSig Addr32)
    (h1 : interpretRef constH c [] = .ok (zeroAddr, [Binding.mk zeroAddr nB]))
    (h2 : interpretRef constH c wZ = .ok (zeroAddr, wZ)) : False := by
  cases c with
  | pure a =>
    have he : ((a, ([] : Word))) = (zeroAddr, [Binding.mk zeroAddr nB]) :=
      Except.ok.inj h1
    exact absurd (Prod.mk.inj he).2 (by simp)
  | vis op k =>
    rw [interpretRef_vis] at h1 h2
    cases op with
    | fail r => simp [referenceHandler] at h1
    | load x => simp [referenceHandler] at h1
    | put m =>
      by_cases hwf : m.WF
      · cases hp : Cas.put constH (Word.toStore []) ⟨m, hwf⟩ with
        | error e => simp [referenceHandler, dif_pos hwf, hp] at h1
        | ok out =>
          cases out with
          | duplicate a =>
            obtain ⟨_, _, hσ⟩ := Cas.put_duplicate_spec hp
            simp [Word.toStore] at hσ
          | conflict a occ => simp [referenceHandler, dif_pos hwf, hp] at h1
          | fresh a σ' =>
            obtain ⟨hrefsok, _, ha, _⟩ := Cas.put_fresh_spec hp
            have haz : a = zeroAddr := ha
            subst haz
            simp only [referenceHandler, dif_pos hwf, hp] at h1
            -- the empty-word run has synchronised onto the word `[⟨a, m⟩]`
            cases hq : Cas.put constH (Word.toStore wZ) ⟨m, hwf⟩ with
            | error e => simp [referenceHandler, dif_pos hwf, hq] at h2
            | ok out2 =>
              cases out2 with
              | conflict a2 occ => simp [referenceHandler, dif_pos hwf, hq] at h2
              | fresh a2 σ2 =>
                obtain ⟨_, hfree, ha2, _⟩ := Cas.put_fresh_spec hq
                rw [show a2 = zeroAddr from ha2] at hfree
                simp [Word.toStore, wZ, Word.find] at hfree
              | duplicate a2 =>
                obtain ⟨_, ha2, hσ2⟩ := Cas.put_duplicate_spec hq
                have ha2z : a2 = zeroAddr := ha2
                subst ha2z
                have hm : m = nA := by
                  have hz : Word.toStore wZ zeroAddr = some nA := rfl
                  rw [hz] at hσ2
                  exact (Option.some.inj hσ2).symm
                subst hm
                simp only [referenceHandler, dif_pos hwf, hq] at h2
                -- both runs are now `k zeroAddr` at the word `wZ`
                rw [show ([] : Word) ++ [Binding.mk zeroAddr nA] = wZ from rfl] at h1
                rw [h1] at h2
                have he : (zeroAddr, [Binding.mk zeroAddr nB]) = (zeroAddr, wZ) :=
                  Except.ok.inj h2
                have := (Prod.mk.inj he).2
                simp [wZ] at this
                exact absurd this.symm nA_ne_nB
      · simp [referenceHandler, hwf] at h1

/-- **THE BREAK.** No clause into `ReaderT Env (Prog CasSig)` satisfies the
catch law — for the graph, fuel and blocks exhibited in §4.3. -/
theorem no_scoped_catch_clause : ¬ ∃ k, ScopeCatchLaw k := by
  rintro ⟨k, hk⟩
  have e1 : interpretRef constH (k (catchGraph, 1) 0 1) []
      = .ok (zeroAddr, [Binding.mk zeroAddr nB]) :=
    (hk constH (catchGraph, 1) 0 1 []).trans rfl
  have e2 : interpretRef constH (k (catchGraph, 1) 0 1) wZ
      = .ok (zeroAddr, wZ) :=
    (hk constH (catchGraph, 1) 0 1 wZ).trans rfl
  exact constH_no_separator (k (catchGraph, 1) 0 1) e1 e2

/-- The same, said about handlers rather than clauses: NO `Handler ScopeSig
(ReaderT Env (Prog CasSig))` — the exhibit's own target — catches. So the
`_hnd` the exhibit's clause drops cannot be picked back up. -/
theorem no_handler_into_ScopeM_catches :
    ¬ ∃ hh : Handler ScopeSig ScopeM,
        ScopeCatchLaw (fun e b h => hh.handle (.catchE b h) e) := by
  rintro ⟨hh, hlaw⟩
  exact no_scoped_catch_clause ⟨_, hlaw⟩

/-- And the exhibit's own handler fails the law concretely, not just abstractly:
at the empty word it reports the body's refusal where the law demands the
handler block's answer. -/
theorem scopeHandler_does_not_catch :
    interpretRef constH (scopeHandler.handle (.catchE 0 1) (catchGraph, 1)) []
        = .error (.noObject zeroAddr)
      ∧ interpretRef constH (runBlocks catchGraph 1 1 []) []
        = .ok (zeroAddr, [Binding.mk zeroAddr nB]) := ⟨rfl, rfl⟩

/-- The counterexample is IMMUNE to the rollback question. `interpretRef`'s
error branch carries no word, so the big-step catch law can only restart the
handler at the word the body started from — but `probe` refuses having changed
nothing, and the small-step run says so: the partial word at the refusal IS the
starting word. A "no-rollback" catch law would demand the same outcome here, so
`no_scoped_catch_clause` is not an artefact of demanding rollback. -/
theorem probe_refuses_without_touching_the_word :
    run constH 1 probe [] = (.refused (.noObject zeroAddr), []) := rfl

/-! ### §4.3b — `ensuring` is broken by the same strictness, and it is
IMPLEMENTED

`catchE` at least announces itself by dropping `_hnd`. `ensuring` does not: its
clause is written with `bind`, which looks like it sequences the finalizer after
the body. It does not. `interpretRef_bind` is error-strict, so the finalizer
runs exactly when the body SUCCEEDS — which is the one case a finalizer is not
needed for. -/

theorem ensuring_never_finalises_a_refusal
    (H : Bytes → Addr32) (g : GProg) (fuel : Nat) (b f : BlockId) (w : Word)
    (e : Refusal) (hb : interpretRef H (runBlocks g fuel b []) w = .error e) :
    interpretRef H (scopeHandler.handle (.ensuring b f) (g, fuel)) w
      = .error e := by
  show interpretRef H ((runBlocks g fuel b []).bind _) w = _
  rw [interpretRef_bind, hb]

/-- The witness: block `0` refuses at the empty word, and block `1`'s put — the
"finalizer" — leaves no trace at all. -/
theorem ensuring_witness :
    interpretRef constH (scopeHandler.handle (.ensuring 0 1) (catchGraph, 1)) []
      = .error (.noObject zeroAddr) := rfl

/-! ### §4.4 — the minimum target monad, exhibited

The obstruction is not the handler TYPE and not the signature: `Handler` and
`Sig` are untouched below. It is the TARGET. `Prog CasSig` is syntax whose
refusals are produced one level down, by the handler, so a program cannot
branch on them. The smallest target in which the clause is writable is the one
that already has the error channel — the estate's own `RefM` — with the
address function moved into the reader, because a `catch` must interpret its
children rather than emit them.

The cost is exactly the two-level story: `elaborate` is no longer a translation
of a scoped program into a store program. `scoped`, `provide` and `ensuring`
survive elaboration into `Prog CasSig`; `catchE` and any observation of
`raise` do not. -/

abbrev EnvR := GProg × Nat × (Bytes → Addr32)
abbrev ScopeR := ReaderT EnvR (StateT Word (Except Refusal))

/-- Still an ORDINARY `Handler`. Only the target changed. -/
def scopeHandlerR : Handler ScopeSig ScopeR where
  handle
    | .catchE body hnd => fun e w =>
        match interpretRef e.2.2 (runBlocks e.1 e.2.1 body []) w with
        | .ok r => .ok r
        | .error _ => interpretRef e.2.2 (runBlocks e.1 e.2.1 hnd []) w
    | .ensuring body fin => fun e w =>
        match interpretRef e.2.2 (runBlocks e.1 e.2.1 body []) w with
        | .ok (a, w') =>
          match interpretRef e.2.2 (runBlocks e.1 e.2.1 fin []) w' with
          | .ok (_, w'') => .ok (a, w'')
          | .error r => .error r
        | .error r => .error r
    | .scoped body => fun e w => interpretRef e.2.2 (runBlocks e.1 e.2.1 body []) w
    | .provide _key body => fun e w =>
        interpretRef e.2.2 (runBlocks e.1 e.2.1 body []) w
    | .raise _err => fun _ _ => .error (.failed "scope: raised")

/-- The catch law, satisfied — by `rfl`. -/
theorem scopeHandlerR_catches (e : EnvR) (b h : BlockId) (w : Word) :
    scopeHandlerR.handle (.catchE b h) e w
      = match interpretRef e.2.2 (runBlocks e.1 e.2.1 b []) w with
        | .ok r => .ok r
        | .error _ => interpretRef e.2.2 (runBlocks e.1 e.2.1 h []) w := rfl

/-- And it RECOVERS on the very witness that defeated `Prog CasSig`: the body
block refuses at the empty word, and the handler block's put is what the
composite reports. -/
theorem scopeHandlerR_recovers :
    scopeHandlerR.handle (.catchE 0 1) (catchGraph, 1, constH) []
      = .ok (zeroAddr, [Binding.mk zeroAddr nB]) := rfl

end Scoped

/-! ## §5 — `wlp` as EffHOL's modality: (Mod-E) is only CONDITIONALLY satisfied

The exhibit's §1 identifies `⟨x ← p⟩ φ` with `wlp`, on the strength of the
discriminating sentence, and remarks in passing that "the sequencing law is
`wp_append`, whose `pre ≠ []` side condition is not a hedge". It does not ask
whether the SAME side condition binds `wlp`. It does — and a second, sharper
condition binds it too.

The elimination rule under test is the sequencing shape:

    ⟨x ← p⟩ φ      φ ⊢ ⟨y ← q⟩ ψ
    ─────────────────────────────  (Mod-E)
        ⟨y ← (x ← p; q)⟩ ψ

read on the estate's carrier, where a computation is a `PProg`, sequencing is
`++`, and the modality is `wlp H · Q`. Two instances of that rule are refuted
below. Both refutations are the ⟸ direction of the composition law — which is
the only direction (Mod-E) uses. -/

section Modality
variable (H : Bytes → Addr32)
open Falsifier

/-- What SURVIVES, first: (Mon) is `wlp_mono`, unconditionally. -/
example : ∀ {Q Q' : WPost}, Q ≤ Q' → ∀ (p : PProg), wlp H p Q ≤ wlp H p Q' :=
  wlp_mono H

/-- What SURVIVES, second: the introduction shape is unconditional too — a
completed run establishes the modality at its own answer. -/
example (p : PProg) (Q : WPost) (w w' : Word) (a : Addr32)
    (h : runP H p w = (.done a, w')) : Q a w' → wlp H p Q w :=
  (wlp_of_done H h).mpr

/-- What SURVIVES, third: the composition law itself, WITH the side condition.
`wpAux_append` is already stated at the fold, so `wlp` inherits it for one line
and the packet owes nothing new here. -/
theorem wlp_append (pre post : PProg) (Q : WPost) (w : Word) (hpre : pre ≠ []) :
    wlp H (pre ++ post) Q w
      ↔ wlp H pre
          (fun _ w' => wpAux H True (PProg.answersFrom H [] pre) post Q w') w := by
  have h := wpAux_append H True [] pre post Q w (Or.inr hpre)
  simpa [wlp] using h

/-- The empty table refuses, so its `wlp` is EVERYTHING — the exhibit's own
discriminator, at the table that is the syntactic unit of `++`. -/
theorem wlp_of_empty_table_is_everything (Q : WPost) (w : Word) : wlp H [] Q w :=
  trivial

/-- **`wlp` INHERITS THE `pre ≠ []` SIDE CONDITION.** At the empty prefix the
composed form is `True` while the whole table's `wlp` is `False`, so the
composition law fails in exactly the direction (Mod-E) needs. This is the
`wlp` twin of `falsifier_empty_prefix`, which the library already carries for
`wp`; the packet has been reading that side condition as a `wp`-only
peculiarity. -/
theorem wlp_falsifier_empty_prefix :
    ∃ (H : Bytes → Addr32) (post : PProg) (Q : WPost) (w : Word),
      wpAux H True [] [] (fun _ w' =>
            wpAux H True (PProg.answersFrom H [] []) post Q w') w
        ∧ ¬ wlp H ([] ++ post) Q w := by
  refine ⟨lenAddr, onePut, WPost.bot, [], trivial, ?_⟩
  intro h
  exact h

/-- **(Mod-E) UNCONDITIONAL IS UNSOUND**, spelled as the rule. Take `p` to be
the empty table: it refuses, so `⟨x ← p⟩ φ` is derivable at EVERY `φ`,
including `⊥` — which is the very sentence §1 uses to pick `wlp` over `wp`. The
second premise is then vacuous, `p ++ q` is `q`, and `⟨y ← q⟩ ψ` is false. The
discriminator that selects `wlp` is what makes unconditional (Mod-E) fail. -/
theorem modE_unsound_at_the_empty_prefix :
    ∃ (H : Bytes → Addr32) (p q : PProg) (φ ψ : WPost) (w : Word),
      wlp H p φ w
        ∧ (∀ a w', φ a w' → wlp H q ψ w')
        ∧ ¬ wlp H (p ++ q) ψ w := by
  refine ⟨lenAddr, [], onePut, WPost.bot, WPost.bot, [], trivial,
    fun _ _ hφ => hφ.elim, ?_⟩
  intro h
  exact h

/-- **AND A SECOND CRACK, AT A NON-EMPTY PREFIX.** `pre ≠ []` repairs the law
only in the history-threaded form `wlp_append` states. Read (Mod-E)'s second
premise the way the rule is written — `⟨y ← q⟩ ψ`, the suffix's OWN modality —
and it fails again, because on a table the suffix's answer indices are
ABSOLUTE: `q` alone dangles where `pre ++ q` resolves, and a dangling operand
refuses, and `wlp` of a refusal is everything. So the modality of the suffix is
not the modality that composes.

This is the `wlp` twin of `falsifier_append_needs_history`, and it is the
harder half: it says the estate's `wlp` is a modality over PAIRS (table,
history), not over tables, and (Mod-E) as EffHOL writes it quantifies over the
wrong thing. -/
theorem modE_unsound_at_a_restarted_history :
    ∃ (H : Bytes → Addr32) (p q : PProg) (φ ψ : WPost) (w : Word),
      wlp H p (fun a w' => φ a w') w
        ∧ (∀ a w', φ a w' → wlp H q ψ w')
        ∧ ¬ wlp H (p ++ q) ψ w := by
  refine ⟨lenAddr, [putA], [putB], WPost.top, WPost.bot, [], ?_,
    fun _ _ _ => ?_, ?_⟩
  · show wlp lenAddr [putA] (fun _ _ => True) []
    exact trivial
  · show wlp lenAddr [putB] WPost.bot _
    exact trivial
  · intro h
    exact h

/-- **THE ROOT OF BOTH CRACKS, NAMED.** `embed` is not a monoid homomorphism
from (`PProg`, `++`, `[]`) to (`Prog`, `bind`, `pure`): the empty table is the
unit of `++` and denotes a REFUSAL, not `pure`. Every (Mod-E) failure above is
this one fact, and it is the same fact `falsifier_empty_prefix` records for
`wp`. A modality over tables inherits it; a modality over `Prog` would not. -/
theorem embed_empty_is_not_a_unit (a : Addr32) :
    interpretRef H (embed ([] : PProg)) []
      ≠ interpretRef H (Prog.pure a : Prog CasSig Addr32) [] := by
  intro h
  exact ok_ne_error _ _ h.symm

end Modality

/-! ## §6 — the new §8, `classifier_finer_than_semantics`: SURVIVES, narrowed

Not in the original remit: `workshop/exhibits.lean` grew a §8 while this run was
in flight. Both halves re-derived here independently, and lifted one rung
FURTHER than the exhibit takes them — the two tables agree at the estate's
big-step face too, not only at `runP`. Then the one thing the exhibit's
statement does not say. -/

section Classifier

def load1 : PProg := [.load (.lit zeroAddr)]
def load2 : PProg := [.load (.lit zeroAddr), .load (.ans 0)]

/-- Independent re-derivation of the exhibit's `runP_agree`. -/
theorem load12_runP_agree (H : Bytes → Addr32) (w : Word) :
    runP H load1 w = runP H load2 w := by
  cases hf : Word.find w zeroAddr with
  | none => simp [runP, runPFrom, load1, load2, PIn.resolve, hf]
  | some n => simp [runP, runPFrom, load1, load2, PIn.resolve, hf]

/-- One rung further than the exhibit takes it: the two tables are equal at
STRATUM 3, the estate's own program equality, not merely at the direct run. So
the antecedent of `EC1-T088` really is met, under the CAS mask. -/
theorem load12_ObsEq (H : Bytes → Addr32) : ObsEq H (embed load1) (embed load2) :=
  ObsEq_embed_of_runP H (load12_runP_agree H)

/-- Independent re-derivation of `envelopes_differ`, decided rather than
simped: the classifier separates them by one dataflow edge. -/
theorem load12_dataflow_differs : PProg.dataflow load1 ≠ PProg.dataflow load2 := by
  decide

/-! Both witnesses are inside the checked injection boundary: `ALGEBRA.md` §12
requires `CasAdmissible` to reject empty and dangling tables, and both of these
are non-empty with closed answer-index dataflow. The counterexample is not
smuggled in through a table `admitCas` would refuse. -/
#guard !load1.isEmpty && !load2.isEmpty
#guard (PProg.envelope load1).dataflowClosed
#guard (PProg.envelope load2).dataflowClosed

/-- **THE NARROWING.** The two tables are equal at `runP` AND at `interpretRef`,
and they DIFFER at fixed fuel: at fuel 2 the shorter is `done` while the longer
is still `running`. The estate rules that status out as an observation —
`Status.isRunning` is documented as "the only status a fuelled run reports that
says nothing about the program" — so §8 stands and `EC1-T088` is refuted.

What it costs: `EC1-A31 ObservationMask` must name fuel explicitly. A mask that
forgot to exclude fixed-fuel status would make these two tables semantically
DISTINCT, and §8's counterexample would evaporate — not because the classifier
got coarser but because the semantics got finer than the estate allows.
`falsifier_fuel_bound_is_tight` is the library's own statement of the same
hazard. -/
theorem load12_differ_at_fixed_fuel (H : Bytes → Addr32) :
    (run H 2 (embed load1) wZ).1.isDone = true
      ∧ (run H 2 (embed load2) wZ).1.isRunning = true := ⟨rfl, rfl⟩

end Classifier

/-! ## Receipts -/

#print axioms empty_table_survives
#print axioms load_last_survives_present
#print axioms load_last_survives_absent
#print axioms dangling_ans_survives
#print axioms toPProg_is_not_semantic
#print axioms toPProg_is_not_entry_stable
#print axioms toPProg_sound
#print axioms blockBody_stable
#print axioms stable_succ
#print axioms stable_le
#print axioms coherent
#print axioms denotes_unique
#print axioms offEnd_never_denotes
#print axioms chain_stable_from_2
#print axioms no_two_fuels_disagree
#print axioms denotes_does_not_determine_the_refusal
#print axioms loop_exhausts_at_0_1_2
#print axioms loop_run_exhausts
#print axioms exhausted_is_the_only_unstable_leaf
#print axioms fuel_zero_is_contentless
#print axioms exhausted_leaf_is_unstable
#print axioms Scoped.constH_no_separator
#print axioms Scoped.no_scoped_catch_clause
#print axioms Scoped.no_handler_into_ScopeM_catches
#print axioms Scoped.scopeHandler_does_not_catch
#print axioms Scoped.probe_refuses_without_touching_the_word
#print axioms Scoped.ensuring_never_finalises_a_refusal
#print axioms Scoped.ensuring_witness
#print axioms Scoped.scopeHandlerR_catches
#print axioms Scoped.scopeHandlerR_recovers
#print axioms wlp_append
#print axioms wlp_of_empty_table_is_everything
#print axioms wlp_falsifier_empty_prefix
#print axioms modE_unsound_at_the_empty_prefix
#print axioms modE_unsound_at_a_restarted_history
#print axioms embed_empty_is_not_a_unit
#print axioms load12_runP_agree
#print axioms load12_ObsEq
#print axioms load12_dataflow_differs
#print axioms load12_differ_at_fixed_fuel

end EffectCoreBreaker
