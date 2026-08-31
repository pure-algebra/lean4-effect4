import Cas.Lang.Wp
import Cas.Lang.Tower

/-!
# Effect Core v1 — `EC1-CE045`, the positive half

## What this file IS

The FORCED REPAIR for `ensuring`, owed by counterexample row `EC1-CE045` of
`.staging/effect-core-v1/COUNTEREXAMPLES.md` §6. That row records only the
NEGATIVE half, proved in `.staging/effect-core-v1/breaker-exhibits.lean` §4.3b
(`ensuring_never_finalises_a_refusal`, `ensuring_witness`): sequencing a
finalizer with ordinary `Prog.bind` runs it exactly when the body SUCCEEDS,
because `interpretRef_bind` is refusal-strict. An `ensuring` written that way
is precisely backwards.

`breaker-exhibits.lean` §4.4 did the parallel repair for `catchE`
(`scopeHandlerR_catches`, `scopeHandlerR_recovers`) by interpreting into an
ADEQUATE TARGET — `ReaderT EnvR (StateT Word (Except Refusal))`, the estate's
own `RefM` with the address function in the reader. This file asks whether that
same target repairs `ensuring`, and answers:

**It does not, and the obstruction is the transformer ORDER.** §1 proves it.
`StateT Word (Except Refusal)`'s error branch is `Except.error r` — it has no
word slot, so a clause that re-raises the body's refusal unchanged is, BY THE
LAW ITSELF, blind to everything the finalizer did on that path. §2 exhibits the
minimum further repair — `ExceptT Refusal (StateT Word Id)`, the same two
layers in the other order, whose refusals carry the partial word — and shows it
is not a new semantics: it is exactly the small-step `run` of `Cas/Lang/Interp.lean`,
word included. §3 proves the four `ensuring` laws there.

Throughout, `Handler` and `Sig` are UNTOUCHED and scoped children stay
`BlockId` data: no `HHandler`, no higher-order handler carrier. This is the
`library/cas/AGENTS.md` ruling — "scoped children elaborate through existing
`Handler`/sum/tower machinery into a target that can observe child failure and
state" — carried one step further than the catch repair needed.

## What this file is NOT

It is NOT part of any Lake target and MUST NOT become one. It adds no
definition to `Cas`, moves no bytes, touches no ledger, and mutates nothing in
`library/`. It does not edit the register row it is owed to; §4 PROPOSES
replacement text, and the packet author owns the register.

## Provenance of §0

`BlockId`, `GTerm`, `GBlock`, `GProg`, `blockBody`, `runBlocks`, `ScopeE`,
`ScopeE.Ans`, `ScopeSig`, `EnvR`, `ScopeR`, `scopeHandlerR`,
`scopeHandlerR_catches`, `zeroAddr`, `nA`, `nB`, `wZ`, `constH`, `probe`,
`hndB` and `catchGraph` are copied VERBATIM — byte-identical, machine-diffed —
from `.staging/effect-core-v1/breaker-exhibits.lean` (§0, §2, §4), which itself
copied the graph carrier from `workshop/exhibits.lean`. Neither file is a
library module, so nothing can be imported across the seam. Any divergence
would void the extension, so nothing here is "improved".

ONE copied declaration differs, and only in its binder: `interpretRef_bind`
takes `(H : Bytes → Addr32)` as an explicit argument here, because the breaker
file carries `H` as a `section variable` and this file has no such section. The
statement and the proof script are otherwise identical.

Names added by THIS file are marked `NEW` in their docstring.

## Fences

- outside every lake target;
- no `sorry`, no `native_decide`, no `axiom`, no `Classical.choice`;
- every address function is a toy (`constH`, `Hlen`); no digest is computed in
  the kernel — `Hlen` reads an encoded LENGTH, the device `Defun.lean` and
  `Cas.Lang.Falsifier` already use.

## How to elaborate it

From `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/counterexamples/EnsuringRepair.lean
```

Expected: elaborates clean, no errors, no warnings. The `#print axioms` block at
the foot is read, not asserted; every line must show `[propext]` or
`[propext, Quot.sound]`.
-/

namespace EnsuringRepair

open Cas.Lang
open Cas (Bytes Addr32 Node Word Binding Ref)

/-! ## §0 — the carrier, copied verbatim -/

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

/-! ### Fixtures, copied verbatim -/

def zeroAddr : Addr32 := Falsifier.zeroAddr

def nA : Node := ⟨0, 0, [], []⟩
def nB : Node := ⟨0, 1, [], []⟩

theorem nA_ne_nB : nA ≠ nB := by decide

/-- A constant address function: every node addresses to `zeroAddr`. Level 0 —
the estate assumes nothing about `H` anywhere. -/
def constH : Bytes → Addr32 := fun _ => zeroAddr

def wZ : Word := [Binding.mk zeroAddr nA]

def probe : Prog CasSig Addr32 := .vis (.load zeroAddr) (fun _ => .pure zeroAddr)
def hndB  : Prog CasSig Addr32 := .vis (.put nB) (fun a => .pure a)

def catchGraph : GProg :=
  ⟨[⟨[.load (.lit zeroAddr)], .ret⟩, ⟨[.put 0 1 [] []], .ret⟩], 0⟩

/-- The big-step bind law, as in the breaker's §2. -/
theorem interpretRef_bind {A B} (H : Bytes → Addr32)
    (p : Prog CasSig A) (f : A → Prog CasSig B) (w : Word) :
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

/-! ### The scoped signature and the catch-adequate target, copied verbatim -/

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

abbrev EnvR := GProg × Nat × (Bytes → Addr32)
abbrev ScopeR := ReaderT EnvR (StateT Word (Except Refusal))

/-- The breaker's §4.4 handler, verbatim: an ORDINARY `Handler`, only the
target changed from `ReaderT Env (Prog CasSig)`. -/
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

/-- The catch law, satisfied — by `rfl`. Copied verbatim; it is the model this
file mirrors, and it is re-elaborated here so §2's conservativity theorem has
its left-hand side standing in the same file. -/
theorem scopeHandlerR_catches (e : EnvR) (b h : BlockId) (w : Word) :
    scopeHandlerR.handle (.catchE b h) e w
      = match interpretRef e.2.2 (runBlocks e.1 e.2.1 b []) w with
        | .ok r => .ok r
        | .error _ => interpretRef e.2.2 (runBlocks e.1 e.2.1 h []) w := rfl

/-! ## §1 — NEW. The catch-adequate target does NOT repair `ensuring`

`breaker-exhibits.lean` §4.4 moved the target from `ReaderT Env (Prog CasSig)`
to `ReaderT EnvR (StateT Word (Except Refusal))` and recovered `catchE`. It did
not fix `ensuring`, and this section proves the failure is not an oversight in
the clause but a property of the target.

Two facts, in order.

**§1.1 — the shipped clause still skips the finalizer.** `scopeHandlerR`'s
`ensuring` clause matches on the body's outcome and returns `.error r`
untouched. So the §4.3b defect survived the catch repair verbatim, one stratum
up.

**§1.2 — and no clause into that target can do better.** State the one half of
the `ensuring` law that is not in dispute: a finalizer must not swallow or
replace the body's refusal. Any clause satisfying that half returns
`Except.error r` on the refusal path, and `Except.error r` has NO word
component — so the clause's observable output there is a function of `r` alone.
Two finalizers that leave demonstrably different words are therefore
indistinguishable. The proof is one rewrite; the triviality IS the content. -/

section Obstruction

/-- NEW. The witness graph. Block `0` is the body — it loads `zeroAddr` and so
REFUSES at the empty word, changing nothing. Blocks `1` and `2` are two
candidate finalizers: both SUCCEED at the empty word and leave DIFFERENT
words. Block `0` and block `1` are `catchGraph`'s two blocks unchanged. -/
def ensGraph : GProg :=
  ⟨[⟨[.load (.lit zeroAddr)], .ret⟩,
    ⟨[.put 0 1 [] []], .ret⟩,
    ⟨[.put 0 0 [] []], .ret⟩], 0⟩

/-- NEW. The three blocks are the ordinary denotations the breaker already
named: the body is `probe`, the first finalizer is `hndB`. -/
theorem ensGraph_body : runBlocks ensGraph 1 0 [] = probe := rfl
theorem ensGraph_finA : runBlocks ensGraph 1 1 [] = hndB := rfl

/-- NEW. The body refuses at the empty word. -/
theorem ensGraph_body_refuses :
    interpretRef constH (runBlocks ensGraph 1 0 []) []
      = .error (.noObject zeroAddr) := rfl

/-- NEW. Both finalizers succeed at the empty word, and their words DIFFER —
one writes `nB` at `zeroAddr`, the other writes `nA`. So there is a real
difference for a target to observe. -/
theorem ensGraph_finalizers_differ :
    interpretRef constH (runBlocks ensGraph 1 1 []) []
        = .ok (zeroAddr, [Binding.mk zeroAddr nB])
      ∧ interpretRef constH (runBlocks ensGraph 1 2 []) [] = .ok (zeroAddr, wZ)
      ∧ ([Binding.mk zeroAddr nB] : Word) ≠ wZ :=
  ⟨rfl, rfl, by simp [wZ, nA_ne_nB.symm]⟩

/-- NEW. §1.1 — the catch repair left `ensuring` exactly as broken as §4.3b
found it: whenever the body refuses, `scopeHandlerR` reports that refusal and
the finalizer block is never consulted, for EVERY graph, fuel, address function
and finalizer. -/
theorem scopeHandlerR_ensuring_still_skips_the_finalizer
    (e : EnvR) (b f : BlockId) (w : Word) (r : Refusal)
    (hb : interpretRef e.2.2 (runBlocks e.1 e.2.1 b []) w = .error r) :
    scopeHandlerR.handle (.ensuring b f) e w = .error r := by
  show (match interpretRef e.2.2 (runBlocks e.1 e.2.1 b []) w with
        | .ok (a, w') =>
          match interpretRef e.2.2 (runBlocks e.1 e.2.1 f []) w' with
          | .ok (_, w'') => Except.ok (a, w'')
          | .error r => .error r
        | .error r => .error r) = _
  rw [hb]
  rfl

/-- NEW. The concrete witness, by `rfl`: the composite reports the body's
refusal, while the finalizer block on its own would have written a binding. -/
theorem scopeHandlerR_ensuring_witness :
    scopeHandlerR.handle (.ensuring 0 1) (ensGraph, 1, constH) []
        = .error (.noObject zeroAddr)
      ∧ interpretRef constH (runBlocks ensGraph 1 1 []) []
        = .ok (zeroAddr, [Binding.mk zeroAddr nB]) := ⟨rfl, rfl⟩

/-- NEW. The half of the `ensuring` law that is not in dispute, as a predicate
on clauses into the catch-adequate target: the finalizer must not swallow or
replace the body's refusal. This is exactly what separates `ensuring` from
`catchE`. -/
def ReRaises (k : EnvR → BlockId → BlockId → Word → Except Refusal (Addr32 × Word)) :
    Prop :=
  ∀ (e : EnvR) (b f : BlockId) (w : Word) (r : Refusal),
    interpretRef e.2.2 (runBlocks e.1 e.2.1 b []) w = .error r →
      k e b f w = .error r

/-- **NEW. THE OBSTRUCTION.** Every clause into `ReaderT EnvR (StateT Word
(Except Refusal))` that re-raises is BLIND to its finalizer on the refusal
path: two different finalizer blocks give the same output. The target's error
branch carries no word, so there is nowhere for a finalizer's effect to be
reported; re-raising fixes the whole observation. -/
theorem reraise_is_finalizer_blind
    (k : EnvR → BlockId → BlockId → Word → Except Refusal (Addr32 × Word))
    (hk : ReRaises k) (e : EnvR) (b f₁ f₂ : BlockId) (w : Word) (r : Refusal)
    (hb : interpretRef e.2.2 (runBlocks e.1 e.2.1 b []) w = .error r) :
    k e b f₁ w = k e b f₂ w := by
  rw [hk e b f₁ w r hb, hk e b f₂ w r hb]

/-- NEW. The obstruction is NOT vacuous: at `ensGraph`, the body refuses and
the two finalizers leave different words, so a clause is forced to identify two
`ensuring`s that a word-carrying observer separates. -/
theorem reraise_blindness_is_not_vacuous
    (k : EnvR → BlockId → BlockId → Word → Except Refusal (Addr32 × Word))
    (hk : ReRaises k) :
    k (ensGraph, 1, constH) 0 1 [] = k (ensGraph, 1, constH) 0 2 []
      ∧ interpretRef constH (runBlocks ensGraph 1 1 [])
          [] ≠ interpretRef constH (runBlocks ensGraph 1 2 []) [] := by
  refine ⟨reraise_is_finalizer_blind k hk _ 0 1 2 [] _ ensGraph_body_refuses, ?_⟩
  obtain ⟨h1, h2, hne⟩ := ensGraph_finalizers_differ
  rw [h1, h2]
  intro hc
  exact hne (congrArg Prod.snd (Except.ok.inj hc))

end Obstruction

/-! ## §2 — NEW. The forced repair: the word must survive the refusal

§1 says the obstruction is that `StateT Word (Except Refusal)` throws the word
away on refusal. The repair is the SAME TWO LAYERS IN THE OTHER ORDER —
`ExceptT Refusal (StateT Word Id)`, i.e. `Word → Except Refusal A × Word`,
where the error branch still carries a word. Transformer order is semantics;
here it is exactly the difference between an `ensuring` that can report what
its finalizer did and one that cannot.

This is NOT a new semantics, and §2.2 proves it twice over:

- against the estate's `interpretRef`: the two agree on every value, every
  word, and every refusal — the new target merely retains, on the error branch,
  the word `interpretRef` discards;
- against the estate's small-step `run`: `interpretRefW` IS `run` past enough
  fuel, WORD INCLUDED. `Cas/Lang/Handler.lean`'s `run_interpretRef_agree` had
  to leave the refusal word existential ("information `Except Refusal (A ×
  Word)` has nowhere to hold"); here it is an equation. The word this target
  reports on a refusal is the estate's own partial word, not an invention.

`Handler` is untouched: `referenceHandlerW` is DEFINED FROM `referenceHandler`
clause by clause, so it cannot drift from the reference meaning, and its
refusal triage `(.error r, w)` is exactly `step`'s — the word the step was
reached with (`Cas/Lang/Handler.lean`, `step_handle`). -/

section WordCarrying

/-- NEW. The word-carrying reference target: `Except` INSIDE the state. -/
abbrev RefW := ExceptT Refusal (StateM Word)

/-- NEW. The same reference semantics, in the word-carrying target. Every
clause is `referenceHandler`'s, re-packaged: an answer continues at the
handler's word, a refusal stops AT THE WORD THE OPERATION WAS REACHED WITH —
`step`'s own triage. Still an ordinary `Handler`. -/
def referenceHandlerW (H : Bytes → Addr32) : Handler CasSig RefW where
  handle op := fun w =>
    match (referenceHandler H).handle op w with
    | .ok (ans, w') => (.ok ans, w')
    | .error r => (.error r, w)

/-- NEW. Word-carrying big-step interpretation: an ordinary `interpret`, so
`interpret_bind` applies to it unchanged. -/
def interpretRefW (H : Bytes → Addr32) {A : Type} (p : Prog CasSig A) (w : Word) :
    Except Refusal A × Word :=
  interpret (referenceHandlerW H) p w

/-- NEW. The clause, unfolded. -/
theorem handleW_eq (H : Bytes → Addr32) (op : CasSig.Op) (w : Word) :
    (referenceHandlerW H).handle op w
      = match (referenceHandler H).handle op w with
        | .ok (ans, w') => (.ok ans, w')
        | .error r => (.error r, w) := rfl

/-- NEW. Done. -/
theorem interpretRefW_pure (H : Bytes → Addr32) {A : Type} (a : A) (w : Word) :
    interpretRefW H (.pure a) w = (.ok a, w) := rfl

/-- NEW. One operation: continue at the handler's word, or STOP AND KEEP IT. -/
theorem interpretRefW_vis (H : Bytes → Addr32) {A : Type} (op : CasSig.Op)
    (k : CasSig.Ans op → Prog CasSig A) (w : Word) :
    interpretRefW H (.vis op k) w
      = match (referenceHandlerW H).handle op w with
        | (.ok ans, w') => interpretRefW H (k ans) w'
        | (.error r, w') => (.error r, w') := by
  cases h : (referenceHandlerW H).handle op w with
  | mk res w' =>
    cases res with
    | ok ans =>
      show (interpret (referenceHandlerW H) (Prog.vis op k)) w = _
      simp only [interpret, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
        StateT.bind, h]
      rfl
    | error r =>
      show (interpret (referenceHandlerW H) (Prog.vis op k)) w = _
      simp only [interpret, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
        StateT.bind, h]
      rfl

/-- NEW. The monad-morphism law, inherited: `RefW` is a lawful stdlib stack, so
`interpret_bind` gives the bind law for free — no new proof, no new carrier. -/
theorem interpretRefW_bind (H : Bytes → Addr32) {A B : Type}
    (p : Prog CasSig A) (f : A → Prog CasSig B) (w : Word) :
    interpretRefW H (p.bind f) w
      = match interpretRefW H p w with
        | (.ok a, w₁) => interpretRefW H (f a) w₁
        | (.error r, w₁) => (.error r, w₁) := by
  have hw := congrArg (fun m => m w) (interpret_bind (referenceHandlerW H) p f)
  simp only [interpretRefW]
  rw [hw]
  cases hp : interpret (referenceHandlerW H) p w with
  | mk res w₁ =>
    cases res with
    | ok a =>
      simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind, hp]
    | error r =>
      simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, StateT.bind, hp]
      rfl

/-! ### §2.2 — adequacy: this is the estate's semantics, not a second one -/

/-- **NEW.** Against `interpretRef`: same value, same success word, same
refusal. The ONLY difference is the word retained on the error branch — which
is precisely the information §1 showed `ensuring` needs. -/
theorem interpretRef_eq_interpretRefW (H : Bytes → Addr32) {A : Type}
    (p : Prog CasSig A) (w : Word) :
    interpretRef H p w
      = match interpretRefW H p w with
        | (.ok a, w') => .ok (a, w')
        | (.error r, _) => .error r := by
  induction p generalizing w with
  | pure a => rfl
  | vis op k ih =>
    rw [interpretRef_vis H op k w, interpretRefW_vis H op k w, handleW_eq]
    cases hh : (referenceHandler H).handle op w with
    | ok aw => obtain ⟨ans, w'⟩ := aw; exact ih ans w'
    | error r => rfl

/-- NEW. Forget the word the new target keeps on refusal — the map back onto
the estate's `interpretRef` face. -/
def forget {A : Type} : Except Refusal A × Word → Except Refusal (A × Word)
  | (.ok a, w) => .ok (a, w)
  | (.error r, _) => .error r

/-- NEW. Adequacy, restated through `forget`: `interpretRef` IS the
word-carrying interpretation with the refusal word forgotten. -/
theorem interpretRef_forget (H : Bytes → Addr32) {A : Type} (p : Prog CasSig A)
    (w : Word) : interpretRef H p w = forget (interpretRefW H p w) := by
  rw [interpretRef_eq_interpretRefW]
  cases interpretRefW H p w with
  | mk res w' => cases res <;> rfl

/-- NEW. The status a word-carrying outcome reports, small-step side. -/
def statusOfW {A : Type} : Except Refusal A × Word → Status CasSig A × Word
  | (.ok a, w) => (.done a, w)
  | (.error r, w) => (.refused r, w)

/-- **NEW. THE BRIDGE.** Past a fuel this theorem produces, the fueled
small-step `run` and the word-carrying big-step interpretation are EQUAL —
status and word, on both the done and the refused branch. `Handler.lean`'s
`run_interpretRef_agree` had to leave the refusal word existential; this target
holds it, so the statement is an equation. The word `interpretRefW` reports on
a refusal is exactly the estate's partial word. -/
theorem run_interpretRefW (H : Bytes → Addr32) {A : Type} (p : Prog CasSig A)
    (w : Word) :
    ∃ fuel : Nat, ∀ f, fuel ≤ f → run H f p w = statusOfW (interpretRefW H p w) := by
  induction p generalizing w with
  | pure a =>
    refine ⟨1, fun f hf => ?_⟩
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rw [interpretRefW_pure]
    simp [run, step, statusOfW]
  | vis op k ih =>
    cases hh : (referenceHandler H).handle op w with
    | error r =>
      refine ⟨1, fun f hf => ?_⟩
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      rw [interpretRefW_vis H op k w, handleW_eq, hh, run, step_handle H op k w, hh]
      rfl
    | ok aw =>
      obtain ⟨ans, w'⟩ := aw
      obtain ⟨fuel, hfuel⟩ := ih ans w'
      refine ⟨fuel + 1, fun f hf => ?_⟩
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      have hstep : step H (.vis op k) w = (.running (k ans), w') := by
        rw [step_handle H op k w, hh]
      rw [run_step_running H hstep f', interpretRefW_vis H op k w, handleW_eq, hh]
      exact hfuel f' (by omega)

/-- NEW. `statusOfW` renames the outcome and keeps the word. -/
theorem statusOfW_word {A : Type} (x : Except Refusal A × Word) :
    (statusOfW x).2 = x.2 := by
  obtain ⟨res, w⟩ := x
  cases res <;> rfl

/-- **NEW. INVARIANT PRESERVATION.** The word-carrying interpretation cannot
un-close a store — INCLUDING on the refusal branch, which is the branch that
only exists in this target. Not re-proved: transported from the estate's
`run_preserves_wf` (ledger L7) across `run_interpretRefW`. -/
theorem interpretRefW_preserves_wf (H : Bytes → Addr32) {A : Type}
    (p : Prog CasSig A) {w : Word} (hw : Cas.Word.wf w = true) :
    Cas.Word.wf (interpretRefW H p w).2 = true := by
  obtain ⟨fuel, hfuel⟩ := run_interpretRefW H p w
  have h := run_preserves_wf H fuel p hw
  rw [hfuel fuel (Nat.le_refl fuel), statusOfW_word] at h
  exact h

end WordCarrying

/-! ## §3 — NEW. `ensuring`, repaired, and the four laws

`ensuringT` is a combinator on the TARGET monad's VALUES. It is not a handler
carrier and it does not change `Handler`: `scopeHandlerW` below still takes
`BlockId` children and interprets their block denotations itself, exactly as
`scopeHandlerR` does. No `HHandler`; no higher-order operation.

Two semantic choices are made here and neither is silent:

- on the REFUSAL path the body's refusal is re-raised UNCHANGED even when the
  finalizer itself refuses. A finalizer may not swallow or replace a refusal;
  that is what distinguishes `ensuring` from `catchE`, and
  `ensuring_never_replaces_the_refusal` states it without a premise on `fin`;
- on the SUCCESS path a refusing finalizer DOES replace the body's success with
  its own refusal. Nothing else is honest: the finalizer failed and no one has
  been told. This is the one asymmetry, and it is stated, not hidden. -/

section Ensuring

/-- NEW. A computation in the word-carrying target, at the answer type every
scoped operation carries. -/
abbrev WComp := Word → Except Refusal Addr32 × Word

/-- NEW. `ensuring`, in the target that can express it: the finalizer runs on
BOTH paths, at the word the body left, and on the refusal path the body's
refusal is what is reported. -/
def ensuringT (body fin : WComp) : WComp := fun w =>
  match body w with
  | (.ok a, w₁) =>
    match fin w₁ with
    | (.ok _, w₂) => (.ok a, w₂)
    | (.error r, w₂) => (.error r, w₂)
  | (.error r, w₁) => (.error r, (fin w₁).2)

/-- NEW. The scoped target: the catch-adequate reader, over the word-carrying
monad instead of the word-forgetting one. -/
abbrev ScopeW := ReaderT EnvR RefW

/-- NEW. Still an ORDINARY `Handler` over the UNCHANGED `ScopeSig`, with
`BlockId` children. Only the target changed — one transformer order further
than `scopeHandlerR`.

One consequence worth naming: the `catchE` clause below restarts the handler
block at the ORIGINAL word `w`, discarding the body's partial word. In
`scopeHandlerR`'s target that was FORCED — the partial word did not exist. Here
it is a CHOICE, because `interpretRefW` hands the partial word over. The choice
made is the one `scopeHandlerR` already made, so `scopeHandlerW_catch_agrees`
holds; a no-rollback `catchE` is now expressible and is NOT proved here. -/
def scopeHandlerW : Handler ScopeSig ScopeW where
  handle
    | .catchE body hnd => fun e w =>
        match interpretRefW e.2.2 (runBlocks e.1 e.2.1 body []) w with
        | (.ok a, w') => (.ok a, w')
        | (.error _, _) => interpretRefW e.2.2 (runBlocks e.1 e.2.1 hnd []) w
    | .ensuring body fin => fun e =>
        ensuringT (interpretRefW e.2.2 (runBlocks e.1 e.2.1 body []))
          (interpretRefW e.2.2 (runBlocks e.1 e.2.1 fin []))
    | .scoped body => fun e w => interpretRefW e.2.2 (runBlocks e.1 e.2.1 body []) w
    | .provide _key body => fun e w =>
        interpretRefW e.2.2 (runBlocks e.1 e.2.1 body []) w
    | .raise _err => fun _ w => (.error (.failed "scope: raised"), w)

/-- NEW. The clause IS the combinator, by `rfl`. -/
theorem scopeHandlerW_ensuring (e : EnvR) (b f : BlockId) :
    scopeHandlerW.handle (.ensuring b f) e
      = ensuringT (interpretRefW e.2.2 (runBlocks e.1 e.2.1 b []))
          (interpretRefW e.2.2 (runBlocks e.1 e.2.1 f [])) := rfl

/-! ### Law 1 — the finalizer runs on success, and the body's result survives -/

/-- NEW, combinator level. -/
theorem ensuringT_ok (body fin : WComp) (w w₁ w₂ : Word) (a v : Addr32)
    (hb : body w = (.ok a, w₁)) (hf : fin w₁ = (.ok v, w₂)) :
    ensuringT body fin w = (.ok a, w₂) := by
  simp only [ensuringT, hb, hf]

/-- **LAW 1 — `ensuring_runs_on_success`.** The body succeeds; the finalizer's
effect IS observed in the resulting word (`w₂`, the finalizer's), and the
body's own result (`a`) is preserved, not the finalizer's (`v`). -/
theorem ensuring_runs_on_success (e : EnvR) (b f : BlockId) (w w₁ w₂ : Word)
    (a v : Addr32)
    (hb : interpretRefW e.2.2 (runBlocks e.1 e.2.1 b []) w = (.ok a, w₁))
    (hf : interpretRefW e.2.2 (runBlocks e.1 e.2.1 f []) w₁ = (.ok v, w₂)) :
    scopeHandlerW.handle (.ensuring b f) e w = (.ok a, w₂) :=
  ensuringT_ok _ _ w w₁ w₂ a v hb hf

/-! ### Law 2 — the finalizer runs on refusal, and the refusal survives -/

/-- NEW, combinator level: the finalizer's word is kept whatever the finalizer
answered, and the body's refusal is what is reported. -/
theorem ensuringT_error (body fin : WComp) (w w₁ w₂ : Word) (r : Refusal)
    (res : Except Refusal Addr32)
    (hb : body w = (.error r, w₁)) (hf : fin w₁ = (res, w₂)) :
    ensuringT body fin w = (.error r, w₂) := by
  simp only [ensuringT, hb, hf]

/-- **LAW 2 — `ensuring_runs_on_refusal`.** The body refuses; the finalizer's
effect is STILL observed (the resulting word is `w₂`, the finalizer's), and the
ORIGINAL refusal `r` is re-raised unchanged. -/
theorem ensuring_runs_on_refusal (e : EnvR) (b f : BlockId) (w w₁ w₂ : Word)
    (r : Refusal) (v : Addr32)
    (hb : interpretRefW e.2.2 (runBlocks e.1 e.2.1 b []) w = (.error r, w₁))
    (hf : interpretRefW e.2.2 (runBlocks e.1 e.2.1 f []) w₁ = (.ok v, w₂)) :
    scopeHandlerW.handle (.ensuring b f) e w = (.error r, w₂) :=
  ensuringT_error _ _ w w₁ w₂ r _ hb hf

/-- NEW. Law 2 again, with NO premise on the finalizer's outcome: whatever the
finalizer answered, its word is what the composite reports and the body's
refusal is what it raises. -/
theorem ensuring_runs_on_refusal_of_any_finalizer (e : EnvR) (b f : BlockId)
    (w w₁ w₂ : Word) (r : Refusal) (res : Except Refusal Addr32)
    (hb : interpretRefW e.2.2 (runBlocks e.1 e.2.1 b []) w = (.error r, w₁))
    (hf : interpretRefW e.2.2 (runBlocks e.1 e.2.1 f []) w₁ = (res, w₂)) :
    scopeHandlerW.handle (.ensuring b f) e w = (.error r, w₂) :=
  ensuringT_error _ _ w w₁ w₂ r res hb hf

/-- **NEW. THE DIFFERENCE FROM `catch`, with NO premise on the finalizer.** A
finalizer cannot swallow a refusal and cannot replace it — not even by refusing
itself. -/
theorem ensuring_never_replaces_the_refusal (body fin : WComp) (w w₁ : Word)
    (r : Refusal) (hb : body w = (.error r, w₁)) :
    (ensuringT body fin w).1 = .error r := by
  simp only [ensuringT, hb]

/-- **NEW. §1's OBSTRUCTION, CLOSED.** On the very witness where every clause
into the catch-adequate target had to identify the two finalizers
(`reraise_blindness_is_not_vacuous`), the word-carrying clause SEPARATES them —
same refusal, different words. -/
theorem ensuring_separates_the_finalizers :
    scopeHandlerW.handle (.ensuring 0 1) (ensGraph, 1, constH) []
        = (.error (.noObject zeroAddr), [Binding.mk zeroAddr nB])
      ∧ scopeHandlerW.handle (.ensuring 0 2) (ensGraph, 1, constH) []
        = (.error (.noObject zeroAddr), wZ)
      ∧ scopeHandlerW.handle (.ensuring 0 1) (ensGraph, 1, constH) []
        ≠ scopeHandlerW.handle (.ensuring 0 2) (ensGraph, 1, constH) [] := by
  refine ⟨rfl, rfl, ?_⟩
  intro hc
  have : ([Binding.mk zeroAddr nB] : Word) = wZ := congrArg Prod.snd hc
  simp [wZ, nA_ne_nB.symm] at this

/-- NEW. And `ensuring` is not `catchE`: on the same witness, `catchE` REPLACES
the refusal with the handler block's answer, while `ensuring` keeps it. -/
theorem ensuring_is_not_catch :
    scopeHandlerW.handle (.catchE 0 1) (ensGraph, 1, constH) []
        = (.ok zeroAddr, [Binding.mk zeroAddr nB])
      ∧ scopeHandlerW.handle (.ensuring 0 1) (ensGraph, 1, constH) []
        = (.error (.noObject zeroAddr), [Binding.mk zeroAddr nB]) := ⟨rfl, rfl⟩

/-- NEW. `scopeHandlerW`'s catch clause, unfolded. -/
theorem scopeHandlerW_catchW (e : EnvR) (b h : BlockId) (w : Word) :
    scopeHandlerW.handle (.catchE b h) e w
      = match interpretRefW e.2.2 (runBlocks e.1 e.2.1 b []) w with
        | (.ok a, w') => (.ok a, w')
        | (.error _, _) => interpretRefW e.2.2 (runBlocks e.1 e.2.1 h []) w := rfl

/-- NEW. The repair is CONSERVATIVE for `catchE`: forget the word the new
target keeps on refusal and `scopeHandlerW` is `scopeHandlerR`, which already
satisfies the catch law (`scopeHandlerR_catches`). Nothing that worked at the
previous transformer order was traded away. -/
theorem scopeHandlerW_catch_agrees (e : EnvR) (b h : BlockId) (w : Word) :
    scopeHandlerR.handle (.catchE b h) e w
      = forget (scopeHandlerW.handle (.catchE b h) e w) := by
  rw [scopeHandlerR_catches, scopeHandlerW_catchW,
    interpretRef_forget e.2.2 (runBlocks e.1 e.2.1 b []) w]
  generalize interpretRefW e.2.2 (runBlocks e.1 e.2.1 b []) w = X
  obtain ⟨res, w'⟩ := X
  cases res with
  | ok a => rfl
  | error r => exact interpretRef_forget e.2.2 (runBlocks e.1 e.2.1 h []) w

/-! ### Law 3 — LIFO: the inner finalizer's effect precedes the outer's

`breaker-exhibits.lean` §4.1 records that scoping in this carrier is exactly
ONE level deep: a scoped child is a `BlockId`, a block body is a `PProg`, and
no `PProg` line performs a scoped operation. So two syntactically nested
`ensuring` OPERATIONS are inexpressible here, and no theorem in this file
pretends otherwise. What IS expressible — and what a nesting rule has to be
about — is the composite of the clause with itself in the target, which is
`ensuringT (ensuringT body fi) fo`. The LIFO statement is about that. -/

/-- NEW. The word an `ensuring` leaves is the finalizer's, on every path — the
one equation the ordering laws are built from. -/
theorem ensuringT_word (body fin : WComp) (w : Word) :
    (ensuringT body fin w).2 = (fin (body w).2).2 := by
  unfold ensuringT
  cases hb : body w with
  | mk res w₁ =>
    cases res with
    | ok a =>
      cases hf : fin w₁ with
      | mk res₂ w₂ => cases res₂ <;> simp [hf]
    | error r => simp

/-- **NEW. INVARIANT PRESERVATION, at the clause.** The word an `ensuring`
leaves is an admitted word on BOTH paths — so the finalizer's write, performed
after a refusal, does not escape the admission discipline. -/
theorem ensuring_preserves_wf (e : EnvR) (b f : BlockId) {w : Word}
    (hw : Cas.Word.wf w = true) :
    Cas.Word.wf (scopeHandlerW.handle (.ensuring b f) e w).2 = true := by
  rw [scopeHandlerW_ensuring, ensuringT_word]
  exact interpretRefW_preserves_wf _ _ (interpretRefW_preserves_wf _ _ hw)

/-- **LAW 3 — LIFO.** In a nested `ensuring`, the word threads
body → INNER finalizer → OUTER finalizer. The inner finalizer's effect is
applied first; the outer sees it. -/
theorem ensuring_LIFO (body fi fo : WComp) (w : Word) :
    (ensuringT (ensuringT body fi) fo w).2 = (fo (fi (body w).2).2).2 := by
  rw [ensuringT_word, ensuringT_word]

/-- NEW. The body's refusal survives BOTH finalizers, unchanged — a nested
`ensuring` is still not a `catch`. -/
theorem ensuring_LIFO_reraises (body fi fo : WComp) (w w₁ : Word) (r : Refusal)
    (hb : body w = (.error r, w₁)) :
    (ensuringT (ensuringT body fi) fo w).1 = .error r := by
  refine ensuring_never_replaces_the_refusal _ fo w ((fi w₁).2) r ?_
  rw [show ensuringT body fi w = (.error r, (fi w₁).2) from
    ensuringT_error body fi w w₁ ((fi w₁).2) r (fi w₁).1 hb rfl]

/-! #### LIFO is not vacuous: the order is observable in the store word

A length-sensitive toy address function separates two nodes whose payloads have
different lengths, so their puts land at different addresses and the word — a
LIST, earliest binding first — records which ran first. This is the estate's
own `EC1-CE006` device (`div2_world_seq_is_not_commutative`) and
`Cas.Lang.Falsifier.lenAddr`; no digest is computed in the kernel. -/

/-- NEW. Length-sensitive toy address function. -/
def Hlen : Bytes → Addr32 :=
  fun bs => ⟨List.replicate 32 (UInt8.ofNat bs.length), by simp⟩

/-- NEW. Body block `0` refuses at the empty word; blocks `1` and `2` are two
finalizers whose puts land at DIFFERENT addresses under `Hlen`. -/
def lifoGraph : GProg :=
  ⟨[⟨[.load (.lit zeroAddr)], .ret⟩,
    ⟨[.put 0 0 [] []], .ret⟩,
    ⟨[.put 0 0 [7] []], .ret⟩], 0⟩

/-- NEW. The inner finalizer, as a target computation. -/
def finI : WComp := interpretRefW Hlen (runBlocks lifoGraph 1 1 [])

/-- NEW. The outer finalizer, as a target computation. -/
def finO : WComp := interpretRefW Hlen (runBlocks lifoGraph 1 2 [])

/-- NEW. The refusing body, as a target computation. -/
def bodyRef : WComp := interpretRefW Hlen (runBlocks lifoGraph 1 0 [])

/-- NEW. Both finalizers succeed and each appends one binding. -/
theorem lifo_finalizers_succeed :
    (finI []).1.isOk = true ∧ (finO []).1.isOk = true
      ∧ (finI []).2.length = 1 ∧ (finO []).2.length = 1 := by decide

/-- NEW. Their word effects DO NOT COMMUTE: running the inner then the outer
leaves a different word from the outer then the inner. So LIFO is a claim with
content in this carrier. -/
theorem lifo_order_is_observable :
    (finO (finI []).2).2 ≠ (finI (finO []).2).2 := by decide

/-- NEW. The body refuses at the empty word, leaving it untouched. -/
theorem lifo_body_refuses : bodyRef [] = (.error (.noObject zeroAddr), []) := rfl

/-- NEW. And it leaves the word untouched, so the finalizers start where the
body started. -/
theorem lifo_body_word : (bodyRef []).2 = ([] : Word) := rfl

/-- **NEW. LIFO, witnessed.** With the refusing body, the nested `ensuring`
still runs BOTH finalizers, in inner-then-outer order, and still re-raises the
body's refusal. Swapping the two finalizers changes the word — so the order the
law names is the order the composite has. -/
theorem ensuring_LIFO_witness :
    (ensuringT (ensuringT bodyRef finI) finO []).2 = (finO (finI []).2).2
      ∧ (ensuringT (ensuringT bodyRef finO) finI []).2 = (finI (finO []).2).2
      ∧ (ensuringT (ensuringT bodyRef finI) finO []).2
          ≠ (ensuringT (ensuringT bodyRef finO) finI []).2
      ∧ (ensuringT (ensuringT bodyRef finI) finO []).1 = .error (.noObject zeroAddr) := by
  refine ⟨by rw [ensuring_LIFO, lifo_body_word],
    by rw [ensuring_LIFO, lifo_body_word], ?_, ?_⟩
  · rw [ensuring_LIFO, ensuring_LIFO, lifo_body_word]
    exact lifo_order_is_observable
  · exact ensuring_LIFO_reraises bodyRef finI finO [] [] _ lifo_body_refuses

/-! ### Law 4 — exactly once

The store cannot witness this by COUNTING. Content addressing makes a put
idempotent: `put n` at a word that already binds `n` at its address is the
identity (`Cas.put`'s `duplicate` outcome), so re-running a store finalizer
leaves the same word — `store_finalizer_is_word_idempotent` shows it on the
§1 witness. Counting bindings would therefore be vacuous.

So exactly-once is stated where it has content: as DEPENDENCE. The composite
depends on the finalizer at EXACTLY ONE word — the word the body left. Not
fewer (it does depend on it there), and not more (a clause that ran the
finalizer a second time would also depend on it at the finalizer's own output,
and `ensuring_reads_the_finalizer_once` would then be false). -/

/-- NEW. The §1 store finalizer is word-idempotent, so a counting argument
would prove nothing. -/
theorem store_finalizer_is_word_idempotent :
    (interpretRefW constH (runBlocks ensGraph 1 1 []) []).2
        = [Binding.mk zeroAddr nB]
      ∧ (interpretRefW constH (runBlocks ensGraph 1 1 []) [Binding.mk zeroAddr nB]).2
        = [Binding.mk zeroAddr nB] := ⟨rfl, rfl⟩

/-- **LAW 4a — AT MOST ONCE.** The composite reads the finalizer only at the
word the body left. Two finalizers agreeing there give the same composite,
however wildly they differ elsewhere — which a double-running clause could not
satisfy. -/
theorem ensuring_reads_the_finalizer_once (body fin fin' : WComp) (w : Word)
    (h : fin (body w).2 = fin' (body w).2) :
    ensuringT body fin w = ensuringT body fin' w := by
  unfold ensuringT
  cases hb : body w with
  | mk res w₁ =>
    rw [hb] at h
    cases res with
    | ok a => simp only [h]
    | error r => simp only [h]

/-- **LAW 4b — AT LEAST ONCE.** The dependence at that word is real: two
finalizers that agree at EVERY OTHER word but differ there give different
composites. So the finalizer is not skipped. -/
theorem ensuring_reads_the_finalizer_at_least_once :
    ∃ (body fin fin' : WComp) (w : Word),
      (∀ v, v ≠ (body w).2 → fin v = fin' v)
        ∧ ensuringT body fin w ≠ ensuringT body fin' w := by
  refine ⟨fun w => (.error (.failed "body"), w),
    fun v => (.ok zeroAddr, v),
    fun v => if v = ([] : Word) then (.ok zeroAddr, wZ) else (.ok zeroAddr, v),
    [], ?_, ?_⟩
  · intro v hv
    simp only [if_neg hv]
  · intro hc
    have : ([] : Word) = wZ := congrArg Prod.snd hc
    simp [wZ] at this

/-- **LAW 4c — NOT TWICE, witnessed.** A second application of the finalizer at
its own output is observable, so `ensuring_reads_the_finalizer_once` is a real
constraint and not a triviality: here the composite's word is the finalizer
applied ONCE, and applying it twice would report a strictly different word. -/
theorem double_run_would_be_observable :
    ∃ (body fin : WComp) (w : Word),
      (ensuringT body fin w).2 = (fin (body w).2).2
        ∧ (fin (fin (body w).2).2).2 ≠ (ensuringT body fin w).2 := by
  refine ⟨fun w => (.error (.failed "body"), w),
    fun v => (.ok zeroAddr, Binding.mk zeroAddr nA :: v), [], ensuringT_word _ _ _, ?_⟩
  rw [ensuringT_word]
  simp

end Ensuring

/-! ## §5 — the assumptions this record stands on

Named, not implied, because the stage gate requires them and because a
`Handler` into a richer target invites exactly the assumptions it does not make.

- **Failure.** The only failure mode is `Refusal`, and it is TERMINAL within a
  store program: `Cas.Lang.CasE.fail` answers `Empty`, so a refused program has
  no continuation by type. `ensuring` does not resume a refused body; it runs
  the finalizer and re-raises.
- **External effects: none.** Every clause here is a total pure function.
  `interpretRefW` is `interpret` into a stdlib transformer stack; no oracle, no
  I/O, no clock. The LLM extension (`Cas.Lang.LlmSig`) is not in scope.
- **Concurrency, delivery, fairness: none, and no theorem here needs them.**
  The word is threaded by one writer in one order; there is no scheduler, no
  interleaving, no partial order, no merge. `ensuring_LIFO` is a statement about
  FUNCTION COMPOSITION in a single thread, not about interruption. A real
  finalizer story under interruption is a different model and is NOT proved
  here.
- **Resources.** Two distinct fuels appear and are not the same quantity: the
  `Nat` in `EnvR` is the graph's BLOCK-recursion fuel (`runBlocks`), and the
  fuel in `run_interpretRefW` is the small-step STEP fuel, produced
  existentially exactly as `Cas/Lang/Handler.lean` produces it, because `Prog`'s
  continuations are host functions and have no structural measure.
- **The address function.** Level 0 throughout: nothing is assumed about `H`.
  Both toys used (`constH`, `Hlen`) are degenerate on purpose, and no digest is
  computed in the kernel.
- **Nesting.** One level, by the carrier (see §4, limit 1).
-/

/-! ## §4 — proposed replacement text for the `EC1-CE045` register row

PROPOSED, not applied: `.staging/effect-core-v1/COUNTEREXAMPLES.md` is owned by
the packet author and is not edited by this file. The row currently records only
the negative half. The forced repair this file establishes is TWO steps, not
one, and the register should say so, because `EC1-CE041`'s repair
(`scopeHandlerR`) is the target a reader would otherwise assume settles this
row too — and it does not.

| ID | Exact statement defeated | Witness | State / consequence |
| --- | --- | --- | --- |
| `EC1-CE045` | Sequencing a finalizer with ordinary `Prog.bind` runs it when the body refuses; and the catch-adequate target `ReaderT EnvR (StateT Word (Except Refusal))` of `EC1-CE041` repairs it. | `ensuring_never_finalises_a_refusal`, `ensuring_witness` (`breaker-exhibits.lean` §4.3b) defeat the first clause. `scopeHandlerR_ensuring_still_skips_the_finalizer` and `reraise_is_finalizer_blind` with `reraise_blindness_is_not_vacuous` (`workshop/counterexamples/EnsuringRepair.lean` §1) defeat the second: in that target `Except.error` carries no word, so EVERY clause that re-raises the body's refusal — the half of the law that distinguishes `ensuring` from `catchE` — is blind to its finalizer on that path, and two finalizers leaving demonstrably different words are identified. | `VERIFIED-KERNEL`; `interpretRef_bind` is refusal-strict, AND `EC1-CE041`'s target is insufficient for finalization even though it is sufficient for catch. The forced repair is the transformer ORDER: `ExceptT Refusal (StateT Word Id)`, whose refusals carry the partial word. `interpretRef_forget` and `run_interpretRefW` show this is the estate's own semantics — `interpretRef` with the refusal word retained, and equal to the small-step `run` WORD INCLUDED, which `run_interpretRef_agree` could only state existentially. `ensuring_runs_on_success` / `ensuring_runs_on_refusal` / `ensuring_never_replaces_the_refusal` / `ensuring_LIFO` / `ensuring_reads_the_finalizer_once` close the law there; `scopeHandlerW_catch_agrees` shows the further move is conservative for `catchE`. Still no `HHandler`: `Handler` and `ScopeSig` are unchanged and children stay `BlockId`. |

Two scope limits the row should carry, because this file proves neither:

1. **Nesting is one level deep in this carrier.** A scoped child is a `BlockId`
   and a block body is a `PProg`, so two syntactically nested `ensuring`
   OPERATIONS cannot be written (`breaker-exhibits.lean` §4.1). `ensuring_LIFO`
   is about the composite of the CLAUSE with itself in the target. Syntactic
   nesting needs a carrier change that is out of this row's scope.
2. **Exactly-once is stated as dependence, not as a count.** Content addressing
   makes store word-effects idempotent on the witness used here
   (`store_finalizer_is_word_idempotent`), so counting bindings would be
   vacuous. Whether EVERY successful store program is word-idempotent is not
   proved in this file.
-/

/-! ## Receipts -/

#print axioms nA_ne_nB
#print axioms interpretRef_bind
#print axioms scopeHandlerR_catches
#print axioms ensGraph_body
#print axioms ensGraph_finA
#print axioms ensGraph_body_refuses
#print axioms ensGraph_finalizers_differ
#print axioms scopeHandlerR_ensuring_still_skips_the_finalizer
#print axioms scopeHandlerR_ensuring_witness
#print axioms reraise_is_finalizer_blind
#print axioms reraise_blindness_is_not_vacuous
#print axioms handleW_eq
#print axioms interpretRefW_pure
#print axioms interpretRefW_vis
#print axioms interpretRefW_bind
#print axioms interpretRef_eq_interpretRefW
#print axioms interpretRef_forget
#print axioms run_interpretRefW
#print axioms statusOfW_word
#print axioms interpretRefW_preserves_wf
#print axioms scopeHandlerW_ensuring
#print axioms ensuringT_ok
#print axioms ensuring_runs_on_success
#print axioms ensuringT_error
#print axioms ensuring_runs_on_refusal
#print axioms ensuring_runs_on_refusal_of_any_finalizer
#print axioms ensuring_never_replaces_the_refusal
#print axioms ensuring_separates_the_finalizers
#print axioms ensuring_is_not_catch
#print axioms scopeHandlerW_catchW
#print axioms scopeHandlerW_catch_agrees
#print axioms ensuringT_word
#print axioms ensuring_preserves_wf
#print axioms ensuring_LIFO
#print axioms ensuring_LIFO_reraises
#print axioms lifo_finalizers_succeed
#print axioms lifo_order_is_observable
#print axioms lifo_body_refuses
#print axioms lifo_body_word
#print axioms ensuring_LIFO_witness
#print axioms store_finalizer_is_word_idempotent
#print axioms ensuring_reads_the_finalizer_once
#print axioms ensuring_reads_the_finalizer_at_least_once
#print axioms double_run_would_be_observable

end EnsuringRepair
