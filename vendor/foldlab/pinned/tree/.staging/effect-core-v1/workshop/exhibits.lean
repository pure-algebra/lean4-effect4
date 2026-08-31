import Cas.Lang.Wp
import Cas.Lang.Tower

/-!
# Effect Core v1 — kernel-checked exhibits

Companion to `../WORKSHOP-RESULTS.md`. Written 2026-08-31 against `56a938fe` plus the
working tree, Lean `leanprover/lean4:v4.33.1`. Same role as
`.staging/algebraic-review/handlers-semantics-exhibits.lean`: a file that
COMPILES, so the claims in the prose have a kernel behind them.

Run it:

```
cd library/cas && lake env lean ../../.staging/effect-core-v1/workshop/exhibits.lean
```

Nothing here is proposed for the library. These are prototypes whose only job
is to decide five design questions the packet leaves PENDING, by making the
answer typecheck or fail to.

| § | Bears on | Finding |
|---|---|---|
| 1 | `EC1-PV01` (EffHOL) | The modality `⟨x ← p⟩ φ` is `wlp`, not `wp`. |
| 2 | `EC1-R05`, `EC1-K15` | `Prog`'s inductivity FORCES the fuel-indexed shape. |
| 3 | `EC1-R02`, `EC1-R04` | A fuel-indexed graph denotation is an ordinary `Prog`. |
| 4 | `EC1-R15`, `EC1-K22`, `EC1-S3` | `runCore (injectCas p) = runP p`, proved. |
| 5 | `EC1-A30`, `EC1-K14` | Coherence is DERIVED, and only at the big-step face. |
| 6 | `EC1-R06`, `EC1-K16` | Scoped bodies need no new handler type. |

Every theorem below reports `[propext, Quot.sound]` — standard axioms, no
`sorryAx`, no `Classical.choice`. The `#print axioms` block at the foot is the
receipt.
-/

namespace EffectCoreV1

open Cas.Lang
open Cas (Bytes Addr32 Node Word)

/-! ## §1 — EffHOL's modality is the estate's `wlp` (`EC1-PV01`)

EffHOL (arXiv:2506.09458, Fig. 5) gives `⟨x ← p⟩ φ` exactly three rules —
(Mod-I), (Mod-E), (Mon) — and §III-C records the discriminating sentence:
"while `⊥` is underivable, `⟨x ← p⟩ ⊥` may be derivable for some `p`".

The estate has BOTH transformers already (`Cas/Lang/Wp.lean`). The sentence
decides which one the modality is. -/

section Modality
variable (H : Bytes → Addr32)

/-- (Mon) is `wlp_mono`; the sequencing law is `wp_append`, whose `pre ≠ []`
side condition is not a hedge — `falsifier_empty_prefix` proves it necessary. -/
example : ∀ {Q Q' : WPost}, Q ≤ Q' → ∀ (p : PProg), wlp H p Q ≤ wlp H p Q' :=
  wlp_mono H

/-- **DISCRIMINATOR, half 1.** `⟨x ← p⟩ ⊥` IS derivable for `wlp`: a program
that always refuses satisfies the modality at the FALSE postcondition. -/
theorem wlp_bot_derivable : wlp H Falsifier.absentLoad WPost.bot [] := by
  have h : runP H Falsifier.absentLoad []
      = (Status.refused (Refusal.noObject Falsifier.zeroAddr), []) := rfl
  exact (wlp_of_refused H (Q := WPost.bot) h).mpr trivial

/-- **DISCRIMINATOR, half 2.** `wp` refutes it universally, so `wp` is NOT
EffHOL's modality. -/
theorem wp_bot_never (p : PProg) (w : Word) : ¬ wp H p WPost.bot w :=
  wp_bot H p w

/-- Consequently the specification logic's modality is `wlp`, and `wp` is that
modality conjoined with totality — a decomposition the estate has already
proved, so the spec-logic slice inherits it rather than deriving it.

**NARROWED 2026-08-31 by the breaker lane.** The identification is PARTIAL.
`wlp` satisfies (Mod-I) and (Mon), and it is the transformer the discriminator
selects — but it does NOT satisfy EffHOL's UNCONDITIONAL (Mod-E).
`wlp_falsifier_empty_prefix` shows `wlp` inherits `wp_append`'s `pre ≠ []` side
condition, and `embed_empty_is_not_a_unit` is the root: the empty table is not a
unit of composition. EffHOL's (Mod-E) is therefore unsound here — defeated by
the same discriminator that selected `wlp` in the first place — and a spec-logic
slice must carry the side condition into the rule. -/
theorem wp_is_modality_and_total (p : PProg) (Q : WPost) (w : Word) :
    wp H p Q w ↔ wlp H p Q w ∧ wp H p WPost.top w :=
  wp_iff_wlp_and_total H p Q w

end Modality

/-! ## §2–§5 — the block graph

The carrier under test. One design choice is load-bearing and everything below
turns on it: **a block's body is a `PProg`** — the L-A table, reused whole,
not a new straight-line form beside it. -/

abbrev BlockId := Nat

/-- A terminator. `brTag` is the scrutinee R14a-P1 admits: a decidable test on
what a `load` ANSWERED, never on a pure value. -/
inductive GTerm where
  | ret
  | jump (b : BlockId)
  | brTag (src : PIn) (tag : UInt8) (t f : BlockId)
  deriving DecidableEq

/-- A block IS an L-A table plus one terminator. Every theorem `Defun.lean`
proves about `body` — the envelope, the sandwich, `runP_frame_sound`,
hash-determination, `encodeProg`/`decodeProg` — applies UNCHANGED. -/
structure GBlock where
  body : PProg
  term : GTerm
  deriving DecidableEq

structure GProg where
  blocks : List GBlock
  entry  : BlockId
  deriving DecidableEq

/-! ### §2 — `Prog`'s inductivity forces the fuel-indexed shape (`EC1-R05`)

Uncomment and Lean refuses, with

```
fail to show termination for EffectCoreV1.unfoldBad
  ... Could not find a decreasing measure.
```

because `jump` may revisit a block. This is not a Lean limitation; it is R1
(`Prog` is inductive, no coinduction) seen from the other side. `EC1-R05`
("permit cycles; define divergence only through unbounded execution") is
therefore a CONSEQUENCE of ratified law, not a preference — which is a
stronger footing than the packet currently claims for it.

```
def unfoldBad (g : GProg) : BlockId → List Addr32 → Prog CasSig Addr32
  | b, env =>
    match g.blocks[b]? with
    | none => failWith "graph: no such block"
    | some blk =>
      (embedFrom env blk.body).bind fun a =>
        match blk.term with
        | .ret => .pure a
        | .jump b' => unfoldBad g b' (env ++ [a])
        | .brTag _ _ t _ => unfoldBad g t (env ++ [a])
```
-/

/-- One block, with the recursive tail ABSTRACTED. Isolating the tail is what
turns coherence (§5) into a one-step lemma instead of an induction that
re-derives the whole unfolding. -/
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

/-- The fuel-indexed unfolding: structural on fuel, so total. -/
def runBlocks (g : GProg) : Nat → BlockId → List Addr32 → Prog CasSig Addr32
  | 0, _, _ => failWith "graph: fuel exhausted"
  | fuel + 1, b, env => blockBody g (runBlocks g fuel) b env

/-- The graph's approximant at a fuel. -/
def denoteG (g : GProg) (fuel : Nat) : Prog CasSig Addr32 :=
  runBlocks g fuel g.entry []

/-! ### §3 — each approximant is an ORDINARY `Prog` (`EC1-R02`, `EC1-R04`)

The payoff of choosing `Prog` as the target of the unfolding rather than a
fresh evaluator: every semantics R10 names applies to a graph with NO
restatement. Each `example` below is the whole argument. -/

example (H : Bytes → Addr32) (g : GProg) (n : Nat) (w : Word) :
    Except Refusal (Addr32 × Word) := interpretRef H (denoteG g n) w

example (H : Bytes → Addr32) (g : GProg) (n fuel : Nat) (w : Word) :
    Status CasSig Addr32 × Word := run H fuel (denoteG g n) w

example (H : Bytes → Addr32) (g g' : GProg) (n : Nat) : Prop :=
  ObsEq H (denoteG g n) (denoteG g' n)

example (g : GProg) (n : Nat) : Prog CasSig Addr32 :=
  interpret replayHandler (denoteG g n) |>.run [] |>.toOption |>.elim
    (failWith "replayed") (fun r => .pure r.1)

/-- Out of fuel is a REFUSAL, by `rfl`. `Status` needs no new arm and the
`Refusal` family needs no new clause — `EC1-A29`'s `live` leaf is expressible
in what the estate already carries. -/
theorem out_of_fuel_refuses (g : GProg) (b : BlockId) (env : List Addr32) :
    runBlocks g 0 b env = failWith "graph: fuel exhausted" := rfl

/-! ### §4 — CAS is a protected sublanguage, PROVED (`EC1-R15`, `EC1-K22`)

`ALGEBRA.md` §12 lists four boundary laws, all PENDING. Two of them fall out of
the body-is-a-`PProg` choice, and the first is a MONAD LAW rather than an
induction. -/

/-- `injectCas` — the L-A table as a one-block graph. -/
def ofPProg (p : PProg) : GProg := ⟨[⟨p, .ret⟩], 0⟩

/-- `projectCas` — the left inverse, on the CAS-only fragment.

**BROKEN 2026-08-31 by the breaker lane** *as `projectCas`*: this matches ONE
literal normal form, so `toPProg_is_not_semantic` exhibits two graphs with the
same `Prog` at every fuel, one projected and one refused — likewise for
`entry ≠ 0`. Incompleteness, not unsoundness: `project_inject` below still
holds and `toPProg_sound` is kept. A real `projectCas` must quotient by graph
normalization first. -/
def toPProg (g : GProg) : Option PProg :=
  match g.blocks, g.entry with
  | [⟨p, .ret⟩], 0 => some p
  | _, _ => none

/-- `projectCas (injectCas p) = p`, by `rfl`. -/
theorem project_inject (p : PProg) : toPProg (ofPProg p) = some p := rfl

/-- **The injection is SYNTACTIC, not merely observational.** A straight-line
table denotes, as a one-block graph at any positive fuel, exactly the program
`embed` already gives it — by `Prog.bind_pure_right`, the monad law
`Representation.lean` proves.

Consequence: every theorem `Defun.lean` proves about `embed p` transfers to
the graph rung with no restatement, and `Fragments.lean`'s owed `L-A ↪ L-S`
row collapses to this line. -/
theorem inject_embed (p : PProg) (fuel : Nat) :
    denoteG (ofPProg p) (fuel + 1) = embed p :=
  Prog.bind_pure_right (embedFrom [] p)

/-- **`runCore (injectCas p) = runP p`** — `ALGEBRA.md` §12's second boundary
law and `EC1-S3`'s exit obligation, at the EXACT fuel bound `Defun.lean`
already proved (`p.length + 1`), with no new fuel accounting. -/
theorem runCore_runP (H : Bytes → Addr32) (p : PProg) (w : Word) :
    run H (p.length + 1) (denoteG (ofPProg p) 1) w = runP H p w := by
  rw [inject_embed p 0]
  exact runP_embed_agree H p w

/-- The same in the estate's own equality, so the CAS observation mask needs
no new definition either. -/
theorem inject_obsEq (H : Bytes → Addr32) (p : PProg) (fuel : Nat) :
    ObsEq H (denoteG (ofPProg p) (fuel + 1)) (embed p) :=
  ObsEq.of_eq H (inject_embed p fuel)

/-! ### §5 — coherence is DERIVED, and only at the big-step face

`ALGEBRA.md` §10.3 makes coherence a FIELD of `EC1-A30 Denotation`:
`m ≤ n → truncate m (prefix n) = prefix m`. This section shows it is a
theorem over carriers the estate already has — and locates the constraint the
packet's §10 triangle does not yet state.

The proof factors through `interpret_bind`, the monad-morphism law proved once
for every handler. That law holds at the BIG-STEP judgment. It does NOT hold at
the fueled `run`: `Cas/Backend/Universal.lean` proves
`run_has_no_composition_law` and `run_composite_outruns_its_parts`. So the
coherence arrow of the semantic triangle must be drawn at `interpretRef`, and a
`run`-indexed coherence statement is the wrong shape — a finding, not a
preference. -/

section Coherence
variable (H : Bytes → Addr32)

/-- The big-step bind law in `RefM`'s spelling. A corollary of
`interpret_bind`; the whole of §5's machinery. -/
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

/-- A refusing program never answers `ok`. -/
theorem failWith_not_ok {A} (r : String) (w : Word) (a : A) (w' : Word) :
    interpretRef H (failWith r : Prog CasSig A) w ≠ .ok (a, w') := by
  intro h
  simp [interpretRef, interpret, failWith, referenceHandler,
    bind, StateT.bind, Except.bind] at h

/-- Big-step refinement between two recursive tails. -/
def Refines (rec rec' : BlockId → List Addr32 → Prog CasSig Addr32) : Prop :=
  ∀ b env w a w', interpretRef H (rec b env) w = .ok (a, w') →
                  interpretRef H (rec' b env) w = .ok (a, w')

/-- ONE STEP is monotone in its tail — the whole content of coherence, with no
fuel reasoning anywhere in the proof. -/
theorem blockBody_mono (g : GProg)
    {rec rec' : BlockId → List Addr32 → Prog CasSig Addr32}
    (hr : Refines H rec rec') :
    Refines H (blockBody g rec) (blockBody g rec') := by
  intro b env w a w' h
  unfold blockBody at h ⊢
  cases hb : g.blocks[b]? with
  | none =>
    rw [hb] at h
    exact absurd h (failWith_not_ok H _ w a w')
  | some blk =>
    rw [hb] at h
    dsimp only at h ⊢
    rw [interpretRef_bind] at h ⊢
    cases hbody : interpretRef H (embedFrom env blk.body) w with
    | error e => rw [hbody] at h; exact absurd h (by simp)
    | ok aw =>
      obtain ⟨a₀, w₀⟩ := aw
      rw [hbody] at h
      dsimp only at h ⊢
      cases hterm : blk.term with
      | ret => rw [hterm] at h; exact h
      | jump b' => rw [hterm] at h; exact hr b' _ w₀ a w' h
      | brTag src tag t f =>
        rw [hterm] at h
        dsimp only at h ⊢
        cases hs : src.resolve (env ++ [a₀]) with
        | none => rw [hs] at h; exact absurd h (failWith_not_ok H _ w₀ a w')
        | some x =>
          rw [hs] at h
          dsimp only at h ⊢
          rw [interpretRef_bind] at h ⊢
          cases hl : interpretRef H (load x) w₀ with
          | error e => rw [hl] at h; exact absurd h (by simp)
          | ok nw =>
            obtain ⟨nd, w₁⟩ := nw
            rw [hl] at h
            dsimp only at h ⊢
            exact hr _ _ w₁ a w' h

/-- **COHERENCE.** What the family decides at fuel `n`, it decides the same way
at `n+1`. No new denotation is minted: the statement is over `interpretRef`. -/
theorem coherent :
    ∀ (n : Nat) (g : GProg), Refines H (runBlocks g n) (runBlocks g (n + 1))
  | 0, _ => fun _ _ w a w' h => absurd h (failWith_not_ok H _ w a w')
  | n + 1, g => blockBody_mono H g (coherent n g)

/-- Coherence at every later fuel: the family is a CHAIN. -/
theorem coherent_le :
    ∀ (m n : Nat) (g : GProg), n ≤ m → Refines H (runBlocks g n) (runBlocks g m)
  | 0, n, _, hle => by
    have : n = 0 := Nat.le_zero.mp hle
    subst this; exact fun _ _ _ _ _ h => h
  | m + 1, n, g, hle => by
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · have ih := coherent_le m n g (Nat.le_of_lt_succ hlt)
      exact fun b env w a w' h => coherent H m g b env w a w' (ih b env w a w' h)
    · have : n = m + 1 := Nat.le_antisymm hle hge
      subst this; exact fun _ _ _ _ _ h => h

/-- The graph's meaning is the colimit of the chain: one `∃`, over existing
carriers, rather than a new projective-family record. -/
def Denotes (g : GProg) (w : Word) (a : Addr32) (w' : Word) : Prop :=
  ∃ n, interpretRef H (denoteG g n) w = .ok (a, w')

/-- **The colimit is a partial FUNCTION.** Two witnessing fuels agree, so
`Denotes` is deterministic — which is what keeps R5's byte-decidable word gate
valid once cycles are admitted. Adequacy is a corollary of coherence, not a
separate obligation. -/
theorem denotes_unique (g : GProg) (w : Word) (a₁ a₂ : Addr32) (w₁ w₂ : Word)
    (h₁ : Denotes H g w a₁ w₁) (h₂ : Denotes H g w a₂ w₂) :
    a₁ = a₂ ∧ w₁ = w₂ := by
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₂, hn₂⟩ := h₂
  have k₁ := coherent_le H (max n₁ n₂) n₁ g (Nat.le_max_left _ _)
    g.entry [] w a₁ w₁ hn₁
  have k₂ := coherent_le H (max n₁ n₂) n₂ g (Nat.le_max_right _ _)
    g.entry [] w a₂ w₂ hn₂
  rw [k₁] at k₂
  have h2 : (a₁, w₁) = (a₂, w₂) := Except.ok.inj k₂
  exact ⟨(Prod.mk.inj h2).1, (Prod.mk.inj h2).2⟩

end Coherence

/-! ## §6 — scoped bodies: what survives, and what BROKE

**CORRECTED 2026-08-31 by the breaker lane** — read this before the section.
`.staging/effect-core-v1/breaker-exhibits.lean` refutes the strong reading of
what follows, and the refutation is right.

WHAT SURVIVES. The signature stays first-order (children are `BlockId`s), so
`Sig` is untouched; `raise` answering `Empty` is untouched; `Handler` as a TYPE
is enough, so no `HHandler` and no higher-order signature functor is needed; and
`Handler.sum` gets its first call site.

WHAT BROKE. The TARGET. `no_scoped_catch_clause` proves that **no** clause into
`ReaderT Env (Prog CasSig)` satisfies the catch law — not the one below, none at
all. The engine is `constH_no_separator`: a store program cannot test for
absence, because a refusal is produced one stratum down by the handler and
`Prog CasSig` has no `Except` to branch on. The minimum target in which the
clause is writable is `ReaderT E (StateT Word (Except Refusal))` — the estate's
own `RefM` with `H` moved into the reader — exhibited there as
`scopeHandlerR_catches` / `scopeHandlerR_recovers`.

The `ensuring` clause below is BROKEN AS WRITTEN and is kept unfixed as the
record: `interpretRef_bind` is error-strict, so the `bind` that looks like it
sequences the finalizer after the body runs it exactly when the body SUCCEEDS —
the one case a finalizer is not needed for
(`ensuring_never_finalises_a_refusal`).

The consequence reaches FORK A: "no new handler type" survives; "the scoped
layer elaborates into `Prog CasSig`" does not — so `Handler.through`, whose
middle must be `Prog T`-valued, does not compose this layer down.

The section is kept verbatim below because a refuted exhibit is evidence.

## §6 (as written, refuted in its target) — scoped and higher-order bodies

`EC1-R06` asks for "named body/exit regions rather than opaque callbacks", and
`EC1-K16` owes direct-handler laws. The literature shape for scoped effects
(the scoped-effects and higher-order-effects lines) is a HIGHER-ORDER signature
functor `(Type → Type) → (Type → Type)` and a handler that receives its children
already interpreted.

The estate does not need it. Because a child is a `BlockId` — first-order data,
the same defunctionalization `PIn.ans` already runs — the signature stays an
ordinary `Sig`, the handler stays an ordinary `Handler`, and the environment the
scoped clauses need is a `ReaderT`. This section is that claim, typechecked. -/

namespace Scoped

/-- Bracketing, failure handling, provision, region: every one carries
children, and every child is a `BlockId`. So this is an ordinary first-order
inductive. -/
inductive ScopeE where
  | catchE   (body handler : BlockId)
  | ensuring (body finalizer : BlockId)
  | scoped   (body : BlockId)
  | provide  (key : Addr32) (body : BlockId)
  | raise    (err : Addr32)

/-- `raise` answers `Empty` — a raised program has no continuation BY TYPE,
exactly as `CasE.fail` already does. `EC1-R09`'s typed-failure channel needs no
new machinery at the carrier. -/
abbrev ScopeE.Ans : ScopeE → Type
  | .catchE _ _   => Addr32
  | .ensuring _ _ => Addr32
  | .scoped _     => Addr32
  | .provide _ _  => Addr32
  | .raise _      => Empty

/-- An ordinary `Sig`. `Cas/Lang/Sig.lean` is untouched. -/
def ScopeSig : Sig := ⟨ScopeE, ScopeE.Ans⟩

/-- Growth by summing signatures — R2's cheap axis, unchanged. -/
def ScopedCasSig : Sig := CasSig ⊕ₛ ScopeSig

/-- The environment the scoped clauses need: the block table and a fuel. -/
abbrev Env := GProg × Nat
abbrev ScopeM := ReaderT Env (Prog CasSig)

/-- A reference semantics for the scoped layer, as an ordinary
`Handler ScopeSig ScopeM`. Every child is reached by resolving its id against
the table the reader carries. No `HHandler`, no higher-order signature. -/
def scopeHandler : Handler ScopeSig ScopeM where
  handle
    | .catchE body _hnd  => fun (g, fuel) => runBlocks g fuel body []
    | .ensuring body fin => fun (g, fuel) =>
        (runBlocks g fuel body []).bind fun a =>
          (runBlocks g fuel fin []).bind fun _ => .pure a
    | .scoped body       => fun (g, fuel) => runBlocks g fuel body []
    | .provide _key body => fun (g, fuel) => runBlocks g fuel body []
    | .raise _err        => fun _ => failWith "scope: raised"

/-- Lifting the store algebra into the same target: also an ordinary handler. -/
def storeInScope : Handler CasSig ScopeM where
  handle op := fun _ => .vis op .pure

/-- The composed semantics is `Handler.sum` — and this is its FIRST call site.
`.staging/algebraic-review/THE-ALGEBRA.md` §1.3 records `Handler.sum` with zero
uses and §3.2 makes the missing injection laws debt rank 2; the scoped layer is
the consumer that retires the "law it or lose it" question (Q5) in the keeping
direction. -/
def scopedCasHandler : Handler ScopedCasSig ScopeM :=
  storeInScope.sum scopeHandler

/-- Elaboration is the EXISTING `interpret`: a scoped program becomes a plain
store program under a table and a fuel. -/
def elaborate (p : Prog ScopedCasSig Addr32) (e : Env) : Prog CasSig Addr32 :=
  interpret scopedCasHandler p e

/-- After elaboration every R10 handler applies unchanged. -/
example (H : Bytes → Addr32) (p : Prog ScopedCasSig Addr32) (e : Env)
    (w : Word) : Except Refusal (Addr32 × Word) :=
  interpretRef H (elaborate p e) w

/-- `EC1-K16`'s monad-morphism law is FREE: `interpret_bind` is proved once for
every handler into every lawful target, and `ReaderT` over `Prog` is lawful. -/
example (p : Prog ScopedCasSig Addr32) (f : Addr32 → Prog ScopedCasSig Addr32) :
    interpret scopedCasHandler (p.bind f)
      = interpret scopedCasHandler p >>= fun a => interpret scopedCasHandler (f a) :=
  interpret_bind scopedCasHandler p f

/-- And the two-level collapse is the EXISTING tower theorem (R12). Read the
scoped layer as a translation into store programs, then handle those:
`Handler.through` composes them and `interpret_through` proves the collapse. -/
example (t : Handler ScopeSig (Prog CasSig)) (h : Handler CasSig (Prog CasSig))
    (p : Prog ScopeSig Addr32) :
    interpret h (interpret t p) = interpret (t.through h) p :=
  interpret_through t h p

end Scoped

/-! ## §7 — COUNTEREXAMPLE: out-of-fuel must not be spelled as a refusal

`ALGEBRA.md` §10.3 gives `EC1-A29 FinApprox` a `live` leaf, distinct from
`halt`. This section proves that distinction is FORCED, and that the obvious
economy — reusing the estate's existing `Refusal.failed` for "out of fuel" —
breaks coherence in the error direction.

The witness needs no computed address: `Defun.lean`'s `putWord_ne_failed` says
a put's refusal is NEVER `.failed`, for every address function, so the
statement holds at every `H`. -/

section Exhausted
variable (H : Bytes → Addr32)

/-- The smallest completing graph: one block, one operand-free put, `ret`. -/
def onePutGraph : GProg := ofPProg [Falsifier.putA]

/-- **The error direction of coherence is FALSE** when out-of-fuel is spelled
as an ordinary refusal. At fuel 0 the graph reports
`Refusal.failed "graph: fuel exhausted"`; at fuel 1 it cannot report that
refusal at all. So a `Refines`-style statement quantified over `.error`
outcomes — which is what `truncate m (prefix n) = prefix m` asserts if `live`
and `halt` share a leaf — has a one-block counterexample.

Consequence for the packet: either `EC1-A29`'s `live` leaf stays genuinely
distinct from every `halt`, or the estate's `Status`/`Refusal` families grow a
DISTINGUISHED exhausted arm. `Status.running` (`Cas/Lang/Interp.lean`) is
already that arm on the small-step side and carries the docstring saying so —
"the only status a fuelled run reports that says nothing about the program" —
so the big-step face is the one missing it. -/
theorem exhausted_is_not_a_refusal :
    run H 2 (denoteG onePutGraph 0) []
        = (.refused (.failed "graph: fuel exhausted"), [])
      ∧ (run H 2 (denoteG onePutGraph 1) []).1
        ≠ .refused (.failed "graph: fuel exhausted") := by
  refine ⟨rfl, ?_⟩
  rw [show denoteG onePutGraph 1 = embed [Falsifier.putA] from inject_embed _ 0,
    show (2 : Nat) = ([Falsifier.putA] : PProg).length + 1 from rfl,
    runP_embed_agree H [Falsifier.putA] []]
  show (runPFrom H [] [Falsifier.putA] []).1 ≠ _
  cases hp : putWord H ⟨0, 0, [], []⟩ [] with
  | error r =>
    have hrun : runPFrom H [] [Falsifier.putA] [] = (Status.refused r, ([] : Word)) := by
      simp [runPFrom, Falsifier.putA, resolveRefs, hp]
    rw [hrun]
    intro hc
    have hr : r = Refusal.failed "graph: fuel exhausted" := Status.refused.inj hc
    exact putWord_ne_failed H (hr ▸ hp)
  | ok aw =>
    obtain ⟨a, w'⟩ := aw
    have hrun : runPFrom H [] [Falsifier.putA] [] = (Status.done a, w') := by
      simp [runPFrom, Falsifier.putA, resolveRefs, hp]
    rw [hrun]
    simp

end Exhausted

/-! ## §9 — the missing half of a symmetric pair (`EC1-T123`)

`Cas/Lang/Wp.lean` anchors `wp` at the big-step judgment
(`wp_iff_interpretRef`, `:629`) and anchors the total triple there too
(`Triple_iff_interpretRef`, `:652`). It anchors `wlp` at the RUN
(`wlp_iff_forall`, `:287`) and at the partial triple (`PartialTriple_iff_wlp`,
`:573`) — but **not** at `interpretRef`. The pair is asymmetric, and the
anchor lane found that `EC1-T123 cas_partial_correctness_bridge` needs exactly
the missing half.

Supplied here so the ask carries its own witness. It is a candidate for
`Cas/Lang/Wp.lean` on its own merits, independent of Effect Core: the gap is in
a symmetric pair the module otherwise completes.

Note what the statement does NOT say. `wlp` is silent on a refusing run by
construction, and the bridge carries no word on the refusal side
(`Handler.lean:105`), so the universal quantifier ranges over successful
outcomes only. That asymmetry is C2 of `WORKSHOP-RESULTS.md`, appearing here as
the shape of a theorem rather than as a caveat. -/

section WlpAnchor
variable (H : Bytes → Addr32)

/-- **The missing anchor.** `wlp` against the reference handler's meaning, in
the universal form `wlp_iff_forall` gives it at the run. -/
theorem wlp_iff_interpretRef (p : PProg) (Q : WPost) (w : Word) :
    wlp H p Q w ↔ ∀ a w', interpretRef H (embed p) w = .ok (a, w') → Q a w' := by
  rw [wlp_iff_forall]
  rcases runP_done_or_refused H p w with ⟨a, w', hs⟩ | ⟨r, w', hs⟩
  · have hb : interpretRef H (embed p) w = .ok (a, w') :=
      interpretRef_of_run_done H (p.length + 1)
        (by rw [runP_embed_agree]; exact hs)
    constructor
    · intro h b w'' hb'
      rw [hb] at hb'
      simp only [Except.ok.injEq, Prod.mk.injEq] at hb'
      obtain ⟨rfl, rfl⟩ := hb'
      exact h a w' hs
    · intro h b w'' hs'
      rw [hs] at hs'
      simp only [Prod.mk.injEq, Status.done.injEq] at hs'
      obtain ⟨rfl, rfl⟩ := hs'
      exact h a w' hb
  · have hb : interpretRef H (embed p) w = .error r :=
      interpretRef_of_run_refused H (p.length + 1)
        (by rw [runP_embed_agree]; exact hs)
    constructor
    · intro _ b w'' hb'
      rw [hb] at hb'
      simp at hb'
    · intro _ b w'' hs'
      rw [hs] at hs'
      simp at hs'

/-- And the partial triple against the big-step judgment — the exact mirror of
`Triple_iff_interpretRef`, which is what `EC1-T123` asks for. -/
theorem PartialTriple_iff_interpretRef (p : PProg) (P : WPre) (Q : WPost) :
    PartialTriple H p P Q
      ↔ ∀ w, P w → ∀ a w', interpretRef H (embed p) w = .ok (a, w') → Q a w' := by
  simp only [PartialTriple_iff_wlp, WPre.le_def]
  exact ⟨fun h w hw => (wlp_iff_interpretRef H p Q w).mp (h w hw),
    fun h w hw => (wlp_iff_interpretRef H p Q w).mpr (h w hw)⟩

end WlpAnchor

/-! ## §8 — the classifier is FINER than the semantics (`EC1-T088`)

Independent re-verification of the anchor lane's contradiction. `EC1-T088` asks
for `SemEq full p q → concreteClass (Denotation p) = concreteClass (Denotation q)`
— that semantic equality determines the classification.

At the CAS sublanguage the estate has both halves and they disagree. Two tables
— one load, versus the same load followed by a load of the FIRST LINE'S ANSWER —
run identically at every word, because the second load resolves to the address
the first already found. Their `PProg.dataflow` differs, because the second names
an answer edge.

This is not a defect. R4 rules that identity hashes PRESENTATIONS, so `classify`
is a function of the syntax, and a syntax-level analysis is entitled to be finer
than the observation. `EC1-T088` asserts the converse and is false. The row wants
restating in the other direction (`classify p = classify q → SemEq p q`) or
dropping. -/

section ClassifierFiner

def a0 : Cas.Addr32 := Falsifier.zeroAddr
def load1 : PProg := [.load (.lit a0)]
def load2 : PProg := [.load (.lit a0), .load (.ans 0)]

/-- Identical direct runs, at every address function and every word. -/
theorem runP_agree (H : Bytes → Addr32) (w : Word) :
    runP H load1 w = runP H load2 w := by
  simp only [runP, runPFrom, load1, load2, PIn.resolve]
  cases hf : Word.find w a0 with
  | none => simp
  | some n => simp [hf]

/-- Different classification. -/
theorem envelopes_differ : PProg.envelope load1 ≠ PProg.envelope load2 := by
  intro h
  have := congrArg Envelope.dataflow h
  simp [PProg.envelope, PProg.dataflow, PProg.dataflowFrom, load1, load2,
    PLine.operands] at this

/-- **The contradiction**, at the observable the R5 gate actually decides. -/
theorem classifier_finer_than_semantics :
    (∀ (H : Bytes → Addr32) (w : Word), runP H load1 w = runP H load2 w)
      ∧ PProg.envelope load1 ≠ PProg.envelope load2 :=
  ⟨runP_agree, envelopes_differ⟩

end ClassifierFiner

/-! ## Receipts -/

#print axioms wlp_bot_derivable
#print axioms wp_bot_never
#print axioms wp_is_modality_and_total
#print axioms out_of_fuel_refuses
#print axioms project_inject
#print axioms inject_embed
#print axioms runCore_runP
#print axioms inject_obsEq
#print axioms interpretRef_bind
#print axioms blockBody_mono
#print axioms coherent
#print axioms coherent_le
#print axioms denotes_unique
#print axioms exhausted_is_not_a_refusal
#print axioms classifier_finer_than_semantics
#print axioms wlp_iff_interpretRef
#print axioms PartialTriple_iff_interpretRef

end EffectCoreV1
