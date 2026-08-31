import Cas.Lang.Lang

/-!
# The sum algebra — signatures compose, and the injections are pinned

PDD-7. Contract packet: `library/cas/contracts/PDD-7.contract.md`.
Owed-ledger item 2 of `.staging/algebraic-review/THE-ALGEBRA.md`
(§2.1 L5/L7/L8, §2.3 L21–L26 and L30/L31, hole §3.2).

**Why this file is under `Cas/Backend/` when nothing in it is backend
code.** The declarations below live in `namespace Cas.Lang`, where
their subjects live; only the module PATH says `Backend`. PDD-7's
fence forbids editing any existing file, and Lake's target graph
leaves exactly one door: `[[lean_lib]] name = "Cas"` carries no
`globs`, so a new `Cas/Lang/Sum.lean` that no module imports would be
built by no target at all and `lake --wfail build` would be green
while never elaborating a line of it. `CasBackend` carries
`globs = ["Cas.Backend.+"]`, is in `defaultTargets`, and is in
`check:cas`'s explicit build list, so a module here is kernel-checked
with zero edits — and `Walk.libraryImports` (`tools/Walk.lean:45-56`)
names the backend leaves individually, so this one is outside the
surface, obligation and law ledgers and moves no bytes. This is
PDD-1's device (`Cas/Backend/Canon.lean`), which PDD-9's ticket names
as the device to use. Moving this module to `Cas.Lang.Sum` is a
one-line lakefile change and a ruling, not a side effect; the packet
records it as owed.

## What the file establishes

`Sig.sum`, `Prog.inl`/`Prog.inr` and `Handler.sum` shipped with zero
theorems between them, so R2's "signatures compose by sum" was two
definitions and an analogy. The gap is not academic: the estate's only
mechanical check on program meaning is the WORD, and the word cannot
see the defect these laws exclude. An injection that performs every
operation TWICE is word-identical to the real one on every store
program — a second `put` of the same node is `duplicate` and leaves
the word unchanged (`Handler.lean:85`), a second `load` is `Word.find`
again, and `fail` answers `Empty` so the doubled node is unreachable.
The statement is therefore the whole of the protection.

Three results carry that weight, and each is stronger than "the law
holds":

- `Handler.sum_unique` — any handler agreeing with `h` on the left
  operations and with `g` on the right IS `h.sum g`.
- `inl_unique_one_target` / `inr_unique_one_target` (and their
  corollaries `Prog.inl_unique` / `Prog.inr_unique`) — any injection
  satisfying `interpret (h.sum g) (ι p) = interpret h p` IS `Prog.inl`.
- `llmOracleHandler_unique_one_program` (and its corollary
  `llmOracleHandler_unique`) — the oracle summand L30 names is the ONLY
  handler that presents `handleLlm` as an interpretation.

So there is no wrong-but-passing implementation to find, in any of the
three places this slice touches. The adversaries are kept in the
`Adversary` section with their refutations, as record rather than as
scratch.

### What makes the categoricity work — corrected

An earlier draft of this docstring said the quantification over EVERY
target monad was the load-bearing detail and "not generality for its
own sake". The independent breaker refuted that
(`contracts/attacks/PDD-7/`, `b509cb20`, HOLE-1), and the correction is
recorded here rather than softened:

- **The law is SYNTACTICALLY categorical.** `Prog.inl_unique`'s proof
  consumes exactly ONE instance of its hypothesis — the INITIAL monad
  `Prog (S ⊕ₛ T)` with the two injection handlers — and at that
  instance the hypothesis is EQUIVALENT to the conclusion, by the same
  two rewrites the proof performs (`syntactic_hyp_iff`). So
  `inl_unique_one_target` is the real theorem and `Prog.inl_unique` is
  its corollary; that is how they are stated below.
- **The lesson is about a PROOF SHAPE, and it is applied uniformly.**
  The finding was never a fact about `Prog.inl`: it is that a
  categoricity whose hypothesis is ∀-quantified while its proof
  consumes one instance — at which hypothesis and conclusion are
  equivalent — states less than it proves. The first fix pass
  corrected only the row the breaker pointed at and left the same
  shape in two others (`AttackAmended.lean` §C, NOTE-7). All three
  ADQ rows now carry the narrowed statement as primary and the
  ∀-quantified one as its corollary: `inl_unique_one_target`,
  `inr_unique_one_target`, `llmOracleHandler_unique_one_program`.
  `Handler.sum_unique` is EXEMPT and provably so — its premises are
  already pointwise-minimal, and the breaker's `sum_unique_iff` shows
  they are an equivalence with neither premise spare.
- **The counting target never enters the categoricity.**
  `StateT Nat Id` is the device of the REFUTATION
  (`doubleInl_not_interpret_inl`) and of nothing else.
- **The quantifier is generality, not mechanism — but it is not free.**
  The honest constraint is provable: the target must RECORD effects.
  `Id` does not, and `narrowing_to_Id_fails` proves ADQ-INL becomes
  FALSE when narrowed to it. The initial monad does.
- **Nothing here says the word gate IS blind.** The old text claimed
  weakening to `RefM` "would make the law exactly as blind as the word
  gate". That needs `ObsEq H (liftCas p) (doubleInl p)`, which this
  slice declines to prove and which the breaker also failed to close.
  It is OPEN in both directions and is not implied.

Prior art, verified rather than trusted: the law rows of
`THE-ALGEBRA.md` §2.1/§2.3, `handlers-semantics.md` C.2 §3 (row 3.3 —
"`Prog.inl`/`Prog.inr` are `interpret` of the injection handlers" — is
the observation that makes `Prog.inl_unique` provable, and it is the
reviewer's, not this file's), and `prog-carrier.md` S1–S10 with the
adversaries of H-2/H-3.

The exhibits file those documents cite
(`handlers-semantics-exhibits.lean`) was gitignored and so unreachable
from this worktree while the proofs below were developed; every one of
them comes from the carriers. Main tracked the file at `b9283eda` and
it is verified against this branch. Five statements overlap and agree:
its §1 `interpret_sum_inl`/`interpret_sum_inr` with `interpret_inl`/
`interpret_inr` here, its §2 `op_bind` with `Prog.op_bind`, its §6
`handleLlm_liftCas` with `handleLlm_liftCas`, and its §3 `handler_ext`
with the private helper below — arrived at independently, same
statements, same proof ideas, so the credit for those five is the
reviewer's as much as this file's. Everything else here — the sum
projections, the morphism and injectivity laws, L30, the injection
handlers, the categoricity theorems, and the adversaries — is new. The
exhibits establish that the named laws are PROVABLE; the question this
file is built around is whether the law set is STRONG ENOUGH, which is
a different question and the one hole §3.2 turns on.

Second prior-art debt, credited in place at each declaration: the
independent breaker's attack record,
`library/cas/contracts/attacks/PDD-7/`. Two passes, both STANDS: the
first at `b509cb20` with two HOLEs, the second at `cf91531c`
(STANDS-AMENDED) with NOTE-7. Every finding was prose against
kernel-checked fact — no theorem in this file was ever false — and all
are fixed above.

Adopted from that record, each credited at its declaration:
`syntactic_hyp_iff`, `inl_unique_one_target`,
`doubleInl_interpret_inl_Id`, `narrowing_to_Id_fails`, `dup` with
`doubleInl_factors`, `handleLlm_bind`, and the `badHandleLlm`
adversary (all `Attack.lean` @ `b509cb20`); then
`syntactic_hyp_iff_inr`, `inr_unique_one_target`, `l30_hyp_iff` and
`llmOracleHandler_unique_one_program` (`AttackAmended.lean` §C @
`cf91531c`), which carry the shape lesson into the two rows the first
fix pass missed. `llmOracleHandler_unique` is the breaker's row from
the first pass, restated in the narrowed form by the second. The
breaker proved each first and this file says so at each one.
-/

namespace Cas.Lang

universe u v

/-! ## Handler extensionality, as a private helper only

Handlers agreeing operation by operation are equal. This is
THE-ALGEBRA's **L16, and that row belongs to PDD-8**, which owns the
universal-property block and is running in parallel. This file needs
the fact as machinery and does not claim the row: the helper is
`private`, is deliberately NOT named `Handler.ext`, and will coexist
with PDD-8's public statement on merge. -/
private theorem handler_eq_of_handle {S : Sig} {M : Type → Type v}
    {h g : Handler S M} (hyp : ∀ op, h.handle op = g.handle op) : h = g := by
  cases h
  cases g
  exact congrArg Handler.mk (funext hyp)

/-! ## §2.1 — the carrier's monad-law stragglers

Three equations that every program in the estate already relies on and
none of which was stated. -/

/-- **L5.** The smart constructor and the raw constructor agree:
performing one operation and continuing is the `vis` node itself.
Every program written under R14a P2 ("programs are authored as smart
constructors composed by `bind`") is a `vis` tree only because of this
equation. -/
theorem Prog.op_bind {S : Sig} {B : Type u} (e : S.Op) (k : S.Ans e → Prog S B) :
    (Prog.op e).bind k = Prog.vis e k := rfl

/-- **L7.** Failure absorbs its continuation. `fail` answers `Empty`,
so the continuation is the empty function and `funext` closes it
vacuously. Every user of `require` assumes this. -/
theorem failWith_bind {A B : Type u} (reason : String) (f : A → Prog CasSig B) :
    (failWith reason).bind f = failWith reason := by
  show Prog.vis (S := CasSig) (A := B) (CasE.fail reason) _
    = Prog.vis (S := CasSig) (A := B) (CasE.fail reason) _
  exact congrArg _ (funext fun e => e.elim)

/-- **L8a.** A satisfied guard is no operation at all. -/
theorem require_true (reason : String) :
    require true reason = Prog.pure () := rfl

/-- **L8b.** A violated guard is exactly the refusal. -/
theorem require_false (reason : String) :
    require false reason = failWith reason := rfl

/-! ## §2.3 — the handler-sum projections -/

/-- **L21.** The summed handler answers a left operation with the left
handler's meaning. -/
theorem Handler.sum_handle_inl {S T : Sig} {M : Type → Type v}
    (h : Handler S M) (g : Handler T M) (op : S.Op) :
    (h.sum g).handle (Sum.inl op) = h.handle op := rfl

/-- **L22.** …and a right operation with the right handler's. This is
the row that kills an implementation which quietly discards `g`. -/
theorem Handler.sum_handle_inr {S T : Sig} {M : Type → Type v}
    (h : Handler S M) (g : Handler T M) (op : T.Op) :
    (h.sum g).handle (Sum.inr op) = g.handle op := rfl

/-- **ADQ-SUM.** L21 and L22 are CATEGORICAL: they do not merely hold
of `Handler.sum`, they DETERMINE it. Any handler on the sum signature
that agrees with `h` on the left operations and with `g` on the right
is `h.sum g` — so no wrong-but-passing composition exists, and the two
adversaries in the `Adversary` section below are refuted by a theorem
rather than by an example. -/
theorem Handler.sum_unique {S T : Sig} {M : Type → Type v}
    (h : Handler S M) (g : Handler T M) (k : Handler (S ⊕ₛ T) M)
    (hl : ∀ op, k.handle (Sum.inl op) = h.handle op)
    (hr : ∀ op, k.handle (Sum.inr op) = g.handle op) :
    k = h.sum g :=
  handler_eq_of_handle fun op =>
    match op with
    | .inl o => hl o
    | .inr o => hr o

/-! ## §2.3 — interpretation through a sum

The law every `liftCas` and `liftRootedCas` consumer assumes, stated
for EVERY target monad and every handler pair. Lawfulness of the
target is not needed: the induction closes by `bind_congr`, which asks
only for `Bind`. -/

/-- **L23.** Interpreting a left-injected program through a summed
handler is interpreting it through the left handler. -/
theorem interpret_inl {S T : Sig} {M : Type → Type v} [Monad M] {A : Type}
    (h : Handler S M) (g : Handler T M) (p : Prog S A) :
    interpret (h.sum g) (Prog.inl (T := T) p) = interpret h p := by
  induction p with
  | pure a => rfl
  | vis e k ih => exact bind_congr ih

/-- **L24.** …and the mirror on the right. -/
theorem interpret_inr {S T : Sig} {M : Type → Type v} [Monad M] {A : Type}
    (h : Handler S M) (g : Handler T M) (q : Prog T A) :
    interpret (h.sum g) (Prog.inr (S := S) q) = interpret g q := by
  induction q with
  | pure a => rfl
  | vis e k ih => exact bind_congr ih

/-! ## §2.3 — the injections are monad morphisms -/

/-- **L25**, unit half: `Prog.inl` preserves `pure`. -/
theorem Prog.inl_pure {S T : Sig} {A : Type u} (a : A) :
    Prog.inl (S := S) (T := T) (Prog.pure a) = Prog.pure a := rfl

/-- **L25**, multiplication half: `Prog.inl` preserves `bind`. Together
with `Prog.inl_pure` this is the monad-morphism square (CATALOG §7.2),
and it is what lets a proof push an injection through a program's
structure instead of re-doing the induction at every site. -/
theorem Prog.inl_bind {S T : Sig} {A B : Type u} (p : Prog S A) (f : A → Prog S B) :
    Prog.inl (T := T) (p.bind f)
      = (Prog.inl (T := T) p).bind (fun a => Prog.inl (T := T) (f a)) := by
  induction p with
  | pure a => rfl
  | vis e k ih =>
    exact congrArg (Prog.vis (S := S ⊕ₛ T) (A := B) (Sum.inl e)) (funext ih)

/-- **L25**, unit half on the right. -/
theorem Prog.inr_pure {S T : Sig} {A : Type u} (a : A) :
    Prog.inr (S := S) (T := T) (Prog.pure a) = Prog.pure a := rfl

/-- **L25**, multiplication half on the right. -/
theorem Prog.inr_bind {S T : Sig} {A B : Type u} (q : Prog T A) (f : A → Prog T B) :
    Prog.inr (S := S) (q.bind f)
      = (Prog.inr (S := S) q).bind (fun a => Prog.inr (S := S) (f a)) := by
  induction q with
  | pure a => rfl
  | vis e k ih =>
    exact congrArg (Prog.vis (S := S ⊕ₛ T) (A := B) (Sum.inr e)) (funext ih)

/-! ## §2.3 — the injections are injective

CATALOG §9.4's obligation: export the observation rather than
representation equality. This is what licenses a client to read
`p.inl = q.inl` back as `p = q`. -/

/-- **L26.** `Prog.inl` is injective. -/
theorem Prog.inl_injective {S T : Sig} {A : Type u} :
    ∀ (p q : Prog S A), Prog.inl (T := T) p = Prog.inl (T := T) q → p = q := by
  intro p
  induction p with
  | pure a =>
    intro q
    cases q with
    | pure b => intro hq; simpa [Prog.inl] using hq
    | vis e' k' => intro hq; simp [Prog.inl] at hq
  | vis e k ih =>
    intro q
    cases q with
    | pure b => intro hq; simp [Prog.inl] at hq
    | vis e' k' =>
      intro hq
      have hq' : Prog.vis (S := S ⊕ₛ T) (Sum.inl e) (fun r => Prog.inl (T := T) (k r))
               = Prog.vis (S := S ⊕ₛ T) (Sum.inl e') (fun r => Prog.inl (T := T) (k' r)) := hq
      injection hq' with he hk
      injection he with he'
      subst he'
      exact congrArg (Prog.vis e) (funext fun r => ih r (k' r) (congrFun (eq_of_heq hk) r))

/-- **L26**, mirror: `Prog.inr` is injective. -/
theorem Prog.inr_injective {S T : Sig} {A : Type u} :
    ∀ (p q : Prog T A), Prog.inr (S := S) p = Prog.inr (S := S) q → p = q := by
  intro p
  induction p with
  | pure a =>
    intro q
    cases q with
    | pure b => intro hq; simpa [Prog.inr] using hq
    | vis e' k' => intro hq; simp [Prog.inr] at hq
  | vis e k ih =>
    intro q
    cases q with
    | pure b => intro hq; simp [Prog.inr] at hq
    | vis e' k' =>
      intro hq
      have hq' : Prog.vis (S := S ⊕ₛ T) (Sum.inr e) (fun r => Prog.inr (S := S) (k r))
               = Prog.vis (S := S ⊕ₛ T) (Sum.inr e') (fun r => Prog.inr (S := S) (k' r)) := hq
      injection hq' with he hk
      injection he with he'
      subst he'
      exact congrArg (Prog.vis e) (funext fun r => ih r (k' r) (congrFun (eq_of_heq hk) r))

/-! ## The injection handlers — and why the injections are not primitive

`handlers-semantics.md` C.2 row 3.3 proposes stating that
`Prog.inl`/`Prog.inr` ARE interpretations, which "makes 3.1/3.2
corollaries of 2.2 and kills the hand-rolled recursions". The proposal
is taken here. Its real value is not consolidation: it is that
`interpret (inlHandler S T)` gives a HANDLER whose sum with
`inrHandler` is the identity handler, and that identity is the bridge
`Prog.inl_unique` crosses. -/

/-- The handler that means every `S` operation as itself, inside the
sum. A value of the shipped `Handler` — no new type. -/
def inlHandler (S T : Sig) : Handler S (Prog (S ⊕ₛ T)) where
  handle op := .vis (Sum.inl op) .pure

/-- The mirror on the right. -/
def inrHandler (S T : Sig) : Handler T (Prog (S ⊕ₛ T)) where
  handle op := .vis (Sum.inr op) .pure

/-- **INJ-H.** The hand-rolled left injection IS an interpretation. -/
theorem interpret_inlHandler {S T : Sig} {A : Type} (p : Prog S A) :
    interpret (inlHandler S T) p = Prog.inl p := by
  induction p with
  | pure a => rfl
  | vis e k ih =>
    show Prog.bind (Prog.vis (S := S ⊕ₛ T) (Sum.inl e) Prog.pure) _ = _
    simp only [Prog.bind]
    exact congrArg (Prog.vis (S := S ⊕ₛ T) (A := A) (Sum.inl e)) (funext ih)

/-- **INJ-H**, mirror. -/
theorem interpret_inrHandler {S T : Sig} {A : Type} (q : Prog T A) :
    interpret (inrHandler S T) q = Prog.inr q := by
  induction q with
  | pure a => rfl
  | vis e k ih =>
    show Prog.bind (Prog.vis (S := S ⊕ₛ T) (Sum.inr e) Prog.pure) _ = _
    simp only [Prog.bind]
    exact congrArg (Prog.vis (S := S ⊕ₛ T) (A := A) (Sum.inr e)) (funext ih)

/-- **SUM-ID.** The two injection handlers sum to the identity handler
on the sum signature. One `rfl` per summand — and the whole of
`Prog.inl_unique` rests on it. -/
theorem sum_inlHandler_inrHandler (S T : Sig) :
    (inlHandler S T).sum (inrHandler S T)
      = (idHandler : Handler (S ⊕ₛ T) (Prog (S ⊕ₛ T))) :=
  handler_eq_of_handle fun op =>
    match op with
    | .inl _ => rfl
    | .inr _ => rfl

/-! ## ADQ-INL — L23 is categorical

The adequacy obligation, discharged rather than argued (CONTRACT.md's
`adequacy` class; the shape PDD-2's `anchor_pins_wp` established).
There is no wrong-but-passing injection: satisfying L23 at every
lawful target and every handler pair FORCES `Prog.inl`, pointwise.

The proof is one instantiation. Take the target to be the sum's own
program type and the handler pair to be the injection handlers; their
sum is the identity handler (`sum_inlHandler_inrHandler`), so the left
side collapses by `interpret_id` to `ι p` and the right side is
`Prog.inl p` by `interpret_inlHandler`.

That instantiation is the WHOLE proof, and the next two declarations
say so outright rather than leaving it to be inferred from the tactic
block. Both are the breaker's, adopted with credit:
`contracts/attacks/PDD-7/Attack.lean` §2 @ `b509cb20`. -/

/-- The hypothesis of ADQ-INL, taken at the ONE instance its proof
consumes, is the conclusion up to two rewrites. Breaker's, adopted:
`contracts/attacks/PDD-7/Attack.lean` §2 @ `b509cb20`. -/
theorem syntactic_hyp_iff {S T : Sig}
    (ι : {A : Type} → Prog S A → Prog (S ⊕ₛ T) A) {A : Type} (p : Prog S A) :
    (interpret ((inlHandler S T).sum (inrHandler S T)) (ι p)
        = interpret (inlHandler S T) p)
      ↔ ι p = Prog.inl p := by
  rw [sum_inlHandler_inrHandler, interpret_id, interpret_inlHandler]

/-- **ADQ-INL, the real statement.** Any injection satisfying L23 at
the INITIAL monad with the two injection handlers — one target, one
handler pair — is `Prog.inl`. Strictly stronger than the ∀-quantified
form below, which is now its corollary.

Breaker's, adopted: `contracts/attacks/PDD-7/Attack.lean` §2 @
`b509cb20` (HOLE-1). The packet's first draft claimed the wide
quantifier was the mechanism; it is not, and this is the theorem that
shows it. -/
theorem inl_unique_one_target {S T : Sig}
    (ι : {A : Type} → Prog S A → Prog (S ⊕ₛ T) A)
    (hι : ∀ {A : Type} (p : Prog S A),
        interpret ((inlHandler S T).sum (inrHandler S T)) (ι p)
          = interpret (inlHandler S T) p)
    {A : Type} (p : Prog S A) : ι p = Prog.inl p :=
  (syntactic_hyp_iff ι p).mp (hι p)

/-- **ADQ-INL**, the ∀-quantified form the packet states — now a
COROLLARY of `inl_unique_one_target`, obtained by instantiating the
quantifier at the one target the proof ever used. -/
theorem Prog.inl_unique {S T : Sig}
    (ι : {A : Type} → Prog S A → Prog (S ⊕ₛ T) A)
    (hι : ∀ (M : Type → Type) [Monad M] [LawfulMonad M]
            (h : Handler S M) (g : Handler T M) {A : Type} (p : Prog S A),
            interpret (h.sum g) (ι p) = interpret h p)
    {A : Type} (p : Prog S A) : ι p = Prog.inl p :=
  inl_unique_one_target ι
    (fun {_} q => hι (Prog (S ⊕ₛ T)) (inlHandler S T) (inrHandler S T) q) p

/-- The `inr` mirror of `syntactic_hyp_iff`. Breaker's, adopted:
`contracts/attacks/PDD-7/AttackAmended.lean` §C1 @ `cf91531c`. -/
theorem syntactic_hyp_iff_inr {S T : Sig}
    (ι : {A : Type} → Prog T A → Prog (S ⊕ₛ T) A) {A : Type} (q : Prog T A) :
    (interpret ((inlHandler S T).sum (inrHandler S T)) (ι q)
        = interpret (inrHandler S T) q)
      ↔ ι q = Prog.inr q := by
  rw [sum_inlHandler_inrHandler, interpret_id, interpret_inrHandler]

/-- **ADQ-INR, the real statement** — the mirror of
`inl_unique_one_target`, in the same primary/corollary form. Breaker's,
adopted: `AttackAmended.lean` §C1 @ `cf91531c`, whose NOTE-7 caught that
the first fix pass corrected the shape only where the finding pointed
and left this row on the old one-shot `rwa`. -/
theorem inr_unique_one_target {S T : Sig}
    (ι : {A : Type} → Prog T A → Prog (S ⊕ₛ T) A)
    (hι : ∀ {A : Type} (q : Prog T A),
        interpret ((inlHandler S T).sum (inrHandler S T)) (ι q)
          = interpret (inrHandler S T) q)
    {A : Type} (q : Prog T A) : ι q = Prog.inr q :=
  (syntactic_hyp_iff_inr ι q).mp (hι q)

/-- **ADQ-INR**, the ∀-quantified form — now a COROLLARY, exactly as on
the left. -/
theorem Prog.inr_unique {S T : Sig}
    (ι : {A : Type} → Prog T A → Prog (S ⊕ₛ T) A)
    (hι : ∀ (M : Type → Type) [Monad M] [LawfulMonad M]
            (h : Handler S M) (g : Handler T M) {A : Type} (q : Prog T A),
            interpret (h.sum g) (ι q) = interpret g q)
    {A : Type} (q : Prog T A) : ι q = Prog.inr q :=
  inr_unique_one_target ι
    (fun {_} r => hι (Prog (S ⊕ₛ T)) (inlHandler S T) (inrHandler S T) r) q

/-! ## §2.3 L30/L31 — `handleLlm` is an interpretation

`Prog.handleLlm` (`Interp.lean:184-187`) hand-rolls the `AgentSig`
split, bypassing `Handler.sum` entirely — one of the three open-coded
sum consumers `handlers-semantics.md` B.9 counts. L30 says the
hand-rolled recursion IS `interpret` of a handler, and the handler is a
VALUE of the existing `Handler` type: no new type is minted. -/

/-- L30's right-hand summand: the oracle, as a handler into store
programs. -/
def llmOracleHandler (oracle : String → String) : Handler LlmSig (Prog CasSig) where
  handle | .infer q => .pure (oracle q)

/-- **L30.** The hand-rolled `AgentSig` split is the interpretation of
`idHandler.sum (llmOracleHandler oracle)`. Stated at `A : Type`, which
is where `interpret` lives — `Handler`'s target is `Type → Type v`. -/
theorem handleLlm_eq_interpret (oracle : String → String) {A : Type}
    (p : Prog AgentSig A) :
    p.handleLlm oracle = interpret (idHandler.sum (llmOracleHandler oracle)) p := by
  induction p with
  | pure a => rfl
  | vis op k ih =>
    match op with
    | .inl e =>
      have hl : Prog.handleLlm oracle (Prog.vis (S := AgentSig) (Sum.inl e) k)
          = Prog.vis (S := CasSig) (A := A) e
              (fun r => Prog.handleLlm oracle (k r)) := rfl
      have hr : interpret (idHandler.sum (llmOracleHandler oracle))
              (Prog.vis (S := AgentSig) (Sum.inl e) k)
          = Prog.vis (S := CasSig) (A := A) e
              (fun r => interpret (idHandler.sum (llmOracleHandler oracle)) (k r)) := rfl
      rw [hl, hr]
      exact congrArg (Prog.vis (S := CasSig) (A := A) e) (funext ih)
    | .inr (.infer q) =>
      have hl : Prog.handleLlm oracle (Prog.vis (S := AgentSig) (Sum.inr (LlmE.infer q)) k)
          = Prog.handleLlm oracle (k (oracle q)) := rfl
      have hr : interpret (idHandler.sum (llmOracleHandler oracle))
              (Prog.vis (S := AgentSig) (Sum.inr (LlmE.infer q)) k)
          = interpret (idHandler.sum (llmOracleHandler oracle)) (k (oracle q)) := rfl
      rw [hl, hr]
      exact ih (oracle q)

/-- **L30** as THE-ALGEBRA states it: an equation between two
functions. -/
theorem handleLlm_eq_interpret_fun (oracle : String → String) (A : Type) :
    (Prog.handleLlm (A := A) oracle)
      = interpret (idHandler.sum (llmOracleHandler oracle)) :=
  funext fun p => handleLlm_eq_interpret oracle p

/-! ### ADQ-L30 — L30's right summand is forced

`llmOracleHandler oracle` is the ONLY handler that presents `handleLlm`
as an interpretation. L30 alone does not say this, and the packet's
first draft omitted the row.

Stated in the same primary/corollary form as the two injections: the
narrowed statement first, the ∀-quantified one as its corollary.
Breaker's throughout — `contracts/attacks/PDD-7/Attack.lean` §5 @
`b509cb20` for the row, and `AttackAmended.lean` §C2 @ `cf91531c` for
the narrowing, whose NOTE-7 caught that the row had been adopted in the
∀-form carrying the very shape HOLE-1 was about. -/

/-- The hypothesis of ADQ-L30, at one operation, IS the conclusion at
that operation. `Prog.bind_pure_right` plays the role `interpret_id`
plays on the injection side. -/
theorem l30_hyp_iff (oracle : String → String)
    (g : Handler LlmSig (Prog CasSig)) (q : String) :
    ((Prog.vis (S := AgentSig) (Sum.inr (LlmE.infer q)) Prog.pure).handleLlm oracle
        = interpret (idHandler.sum g)
            (Prog.vis (S := AgentSig) (Sum.inr (LlmE.infer q)) Prog.pure))
      ↔ g.handle (LlmE.infer q) = (llmOracleHandler oracle).handle (LlmE.infer q) := by
  show (Prog.pure (oracle q) = (g.handle (LlmE.infer q)).bind Prog.pure)
    ↔ (g.handle (LlmE.infer q) = Prog.pure (oracle q))
  rw [Prog.bind_pure_right]
  exact eq_comm

/-- **ADQ-L30, the real statement.** The oracle summand is forced by the
hypothesis at SINGLE-OPERATION programs alone — one program per
operation, at `A := String`. Strictly stronger than the ∀-quantified
row below. -/
theorem llmOracleHandler_unique_one_program (oracle : String → String)
    (g : Handler LlmSig (Prog CasSig))
    (hg : ∀ q : String,
        (Prog.vis (S := AgentSig) (Sum.inr (LlmE.infer q)) Prog.pure).handleLlm oracle
          = interpret (idHandler.sum g)
              (Prog.vis (S := AgentSig) (Sum.inr (LlmE.infer q)) Prog.pure)) :
    g = llmOracleHandler oracle :=
  handler_eq_of_handle fun op =>
    match op with
    | LlmE.infer q => (l30_hyp_iff oracle g q).mp (hg q)

/-- **ADQ-L30**, the ∀-quantified form — now a COROLLARY, by the same
structure as `Prog.inl_unique` and `Prog.inr_unique`. -/
theorem llmOracleHandler_unique (oracle : String → String)
    (g : Handler LlmSig (Prog CasSig))
    (hg : ∀ (A : Type) (p : Prog AgentSig A),
        p.handleLlm oracle = interpret (idHandler.sum g) p) :
    g = llmOracleHandler oracle :=
  llmOracleHandler_unique_one_program oracle g (fun _q => hg String _)

/-- **L32**, which THE-ALGEBRA lists as ASSERTED and the packet's first
draft left OWED: `handleLlm` respects `bind`. Two lines from L30 plus
core `interpret_bind` at the shipped `LawfulMonad (Prog S)` — no
induction of its own.

This DISCHARGES the estate's standing assertion at `Interp.lean:19,
181-183` ("interprets by monad morphism"), which is prose with no
declaration behind it anywhere in `library/cas`. Nothing in this slice
depended on that assertion; this supplies what it was claiming.

Breaker's, adopted: `contracts/attacks/PDD-7/Attack.lean` §5 @
`b509cb20`. -/
theorem handleLlm_bind (oracle : String → String) {A B : Type}
    (p : Prog AgentSig A) (f : A → Prog AgentSig B) :
    (p.bind f).handleLlm oracle
      = (p.handleLlm oracle).bind (fun a => (f a).handleLlm oracle) := by
  simp only [handleLlm_eq_interpret]
  exact interpret_bind (idHandler.sum (llmOracleHandler oracle)) p f

/-- **L31.** Lifting a store program into the agent language and
handling inference away returns the program itself, on the nose.
Proved by direct induction, so it holds at every universe — unlike
L30, which `interpret` pins to `Type`.

**Its reach stops at `Prog.inl`'s image, and it is NOT a client
guarantee on its own.** An earlier draft called this "the law every
`runAgent` client assumes", which reads as one. It is not:
`liftCas p` contains no `infer` node, so L31 says nothing whatever
about the oracle, and `Adversary.badHandleLlm` — which DISCARDS the
oracle entirely — satisfies it at every universe. A client wanting an
oracle guarantee must cite **L30** (`handleLlm_eq_interpret`), which is
what kills that adversary. Breaker's finding:
`contracts/attacks/PDD-7/` @ `b509cb20`, HOLE-2. -/
theorem handleLlm_liftCas (oracle : String → String) {A : Type u} (p : Prog CasSig A) :
    (liftCas p).handleLlm oracle = p := by
  induction p with
  | pure a => rfl
  | vis e k ih => exact congrArg (Prog.vis e) (funext ih)

/-- **L31**, re-derived from this packet's own laws rather than by
induction: L30 turns `handleLlm` into an interpretation, L23 discards
the right summand, and `interpret_id` collapses the rest. Kept because
a law set whose members do not compose is a law set that was never
used — this is the mechanical check that they do. -/
theorem handleLlm_liftCas_via_laws (oracle : String → String) {A : Type}
    (p : Prog CasSig A) :
    (liftCas p).handleLlm oracle = p := by
  rw [handleLlm_eq_interpret oracle (liftCas p)]
  show interpret (idHandler.sum (llmOracleHandler oracle)) (Prog.inl p) = p
  rw [interpret_inl, interpret_id]

/-! ## The adversaries

Attack artifacts are record, never scratch (BREAKER.md). Each
adversary below is a wrong implementation that the estate's own gates
could not distinguish before this file existed; each is kept beside
the theorem that kills it, so a later hand cannot relax a law back
without a red build.

The observation the refutations rely on is deliberate. `CasSig`'s
handlers cannot be counted at the WORD — that is the whole content of
hole §3.2 — so the counting is done in a target monad where an
operation is visible: a handler that increments a state.

**The recipe does not transfer to `CasSig` as written.** Breaker's
NOTE-2 (`contracts/attacks/PDD-7/` @ `b509cb20`):
`Handler CasSig (StateT Nat Id)` is UNINHABITED, because `CasE.fail`
answers `Empty` and `Id` has no branch to put it in. The counting
target below is therefore available only at the toy `TickSig`; the
refutations remain sound, since each refutes a ∀-statement and one
witness anywhere suffices. A reader carrying the recipe to the store
language needs `StateT Nat (Except Unit)` instead — the breaker built
exactly that to attack `CasSig` directly. -/

namespace Adversary

/-- A one-operation signature whose answers carry nothing, so that the
only thing a handler for it can do is have an effect. -/
def TickSig : Sig := ⟨Unit, fun _ => Unit⟩

/-- The counting target: state is the operation count. -/
abbrev Counter := StateT Nat Id

/-- Each operation costs one. -/
def tickHandler : Handler TickSig Counter where
  handle _ := fun n => ((), n + 1)

/-- A second, distinguishable handler — each operation costs two. -/
def tickHandler2 : Handler TickSig Counter where
  handle _ := fun n => ((), n + 2)

/-- The one-operation program. -/
def tick : Prog TickSig Unit := .vis () .pure

/-! ### Adversary 1 — the arm-swapping sum

`handlers-semantics.md` B.9's own witness: with no law stated about
`Handler.sum`, an implementation that exchanges the arms when
`S = T` satisfies everything known about it. L21 kills it, and
`Handler.sum_unique` kills the whole family it belongs to. -/

/-- The sum with its arms exchanged. -/
def swapSum {S : Sig} {M : Type → Type v} (h g : Handler S M) : Handler (S ⊕ₛ S) M where
  handle
    | .inl op => g.handle op
    | .inr op => h.handle op

theorem swapSum_left_count :
    ((swapSum tickHandler tickHandler2).handle (Sum.inl ())) 0 = ((), 2) := rfl

theorem tickHandler_count : (tickHandler.handle ()) 0 = ((), 1) := rfl

/-- **Falsifier for L21.** The arm-swapping sum refutes the left
projection: the composed handler answers a LEFT operation with the
RIGHT handler's meaning, and at a counting target that difference is
visible. -/
theorem swapSum_not_sum_handle_inl :
    ¬ (∀ (S : Sig) (M : Type → Type) [Monad M] (h g : Handler S M) (op : S.Op),
         (swapSum h g).handle (Sum.inl op) = h.handle op) := by
  intro hyp
  have h1 := congrFun (hyp TickSig Counter tickHandler tickHandler2 ()) 0
  rw [swapSum_left_count, tickHandler_count] at h1
  have h2 : (2 : Nat) = 1 := congrArg Prod.snd h1
  omega

/-! ### Adversary 2 — the sum that discards its right handler

THE-ALGEBRA §3.2 ADVERSARY 1, verbatim in shape: a handler on
`AgentSig` built from a `CasSig` handler alone, answering every
`infer` with the empty string. It typechecks, it discards `g`, and
before this file it violated no stated law.

The point of the two positive theorems below is to show WHICH law does
the work: the adversary satisfies the L21 and L23 analogues exactly,
so every store-only program is interpreted correctly by it, and only
the right-hand projection (L22/L24) separates it from the truth. That
is why §3.2 says the word gate is blind by construction — a
`CasSig`-only program cannot tell the difference. -/

def badAgentSum {M : Type → Type v} [Monad M] (h : Handler CasSig M) :
    Handler AgentSig M where
  handle
    | .inl op => h.handle op
    | .inr (.infer _) => pure ""

/-- The adversary satisfies L21. -/
theorem badAgentSum_handle_inl {M : Type → Type v} [Monad M]
    (h : Handler CasSig M) (op : CasSig.Op) :
    (badAgentSum h).handle (Sum.inl op) = h.handle op := rfl

/-- The adversary satisfies L23 — every store-only program is
interpreted exactly right, which is the whole reason no run gate
catches it. -/
theorem badAgentSum_interpret_inl {M : Type → Type v} [Monad M]
    (h : Handler CasSig M) {A : Type} (p : Prog CasSig A) :
    interpret (badAgentSum h) (Prog.inl p) = interpret h p := by
  induction p with
  | pure a => rfl
  | vis e k ih => exact bind_congr ih

/-- A store handler that refuses everything — enough to instantiate
the adversary, since `CasE.fail` answers `Empty` and so needs a target
with an error branch. -/
def refuseCas : Handler CasSig (Except Unit) where
  handle
    | .put _ => .error ()
    | .load _ => .error ()
    | .fail _ => .error ()

/-- An oracle that is observably not the empty string. -/
def echoLlm : Handler LlmSig (Except Unit) where
  handle | .infer s => .ok (s ++ "!")

def askX : Prog LlmSig String := .vis (.infer "x") .pure

theorem badAgentSum_askX :
    interpret (badAgentSum refuseCas) (Prog.inr askX) = Except.ok "" := rfl

theorem echoLlm_askX : interpret echoLlm askX = Except.ok "x!" := rfl

/-- **Falsifier for L24.** The discarding sum refutes the right
projection. Together with `badAgentSum_interpret_inl` above this is the
adequacy statement in full: the adversary passes every left-hand law
and fails only here. -/
theorem badAgentSum_not_interpret_inr :
    ¬ (∀ (M : Type → Type) [Monad M] (h : Handler CasSig M) (g : Handler LlmSig M)
         (A : Type) (q : Prog LlmSig A),
         interpret (badAgentSum h) (Prog.inr q) = interpret g q) := by
  intro hyp
  have h1 := hyp (Except Unit) refuseCas echoLlm String askX
  rw [badAgentSum_askX, echoLlm_askX] at h1
  injection h1 with h2
  exact absurd h2 (by decide)

/-! ### Adversary 3 — the doubling injection

THE-ALGEBRA §3.2 ADVERSARY 2 and `prog-carrier.md` H-3, the ticket's
named canonical wrong-but-passing candidate: an injection that
performs every operation TWICE and keeps the first answer. On the
store language the doubling is invisible at the word, so the estate's
only mechanical check on program meaning cannot in principle see it.

What separates it is L23, at a handler that counts. -/

/-- Performs every operation twice, keeps the first answer. -/
def doubleInl {S T : Sig} {A : Type u} : Prog S A → Prog (S ⊕ₛ T) A
  | .pure a => .pure a
  | .vis e k => .vis (Sum.inl e) fun r => .vis (Sum.inl e) fun _ => doubleInl (k r)

theorem doubleInl_tick_count :
    (interpret (tickHandler.sum tickHandler) (doubleInl (T := TickSig) tick)) 0
      = ((), 2) := rfl

theorem inl_tick_count :
    (interpret (tickHandler.sum tickHandler) (Prog.inl (T := TickSig) tick)) 0
      = ((), 1) := rfl

/-- **Falsifier for L23**, fired by the adversary against itself: the
doubling injection does not satisfy the left interpretation law. The
witness is the operation COUNT — two where the real injection spends
one — which is exactly the observation the word gate cannot make. -/
theorem doubleInl_not_interpret_inl :
    ¬ (∀ (S T : Sig) (M : Type → Type) [Monad M] (h : Handler S M) (g : Handler T M)
         (A : Type) (p : Prog S A),
         interpret (h.sum g) (doubleInl (T := T) p) = interpret h p) := by
  intro hyp
  have h1 := congrFun
    (hyp TickSig TickSig Counter tickHandler tickHandler Unit tick) 0
  rw [doubleInl_tick_count] at h1
  rw [show interpret tickHandler tick = (interpret (tickHandler.sum tickHandler)
        (Prog.inl (T := TickSig) tick)) from
      (interpret_inl tickHandler tickHandler tick).symm, inl_tick_count] at h1
  have h2 : (2 : Nat) = 1 := congrArg Prod.snd h1
  omega

/-! #### What L25 contributes to killing it — nothing

THE-ALGEBRA §3.2 and `prog-carrier.md` H-3 both record the doubling
injection as "KILLED BY interpret_inl (L23) together with `inl` is a
monad morphism (L25); nothing weaker separates them."

The second half of that sentence is false, and the two theorems below
are the witness: `doubleInl` IS a monad morphism. It preserves `pure`
and it preserves `bind`, by the same induction the real injection
uses. So L25 excludes it from nothing, and L23 is not merely the first
conjunct of the separating pair — it is the whole of it, as
`Prog.inl_unique` independently shows by pinning `Prog.inl` from L23
alone.

**Read the heading as scoped, and no wider** (breaker's NOTE-3). "L25
excludes THE ADVERSARY from nothing" is what is true; "L25 excludes
nothing" would be false. The breaker's own injections — one that
REORDERS two operations, one that ELIDES an operation whose answer is
unused — die to L25 and L26 respectively. Those laws earn their place;
they are idle against `doubleInl` specifically, and
`doubleInl_factors` below says exactly which family they cannot see.

This is recorded in the packet's break ledger. The finding does not
weaken anything: both laws are true and both are worth having. What
falls is the record's account of which law does the work. -/

/-- The adversary preserves `pure`. -/
theorem doubleInl_pure {S T : Sig} {A : Type u} (a : A) :
    doubleInl (S := S) (T := T) (Prog.pure a) = Prog.pure a := rfl

/-- The adversary preserves `bind`. With `doubleInl_pure`, the doubling
injection satisfies L25 in full — which is why L25 cannot be what
separates it from `Prog.inl`. -/
theorem doubleInl_bind {S T : Sig} {A B : Type u} (p : Prog S A) (f : A → Prog S B) :
    doubleInl (T := T) (p.bind f)
      = (doubleInl (T := T) p).bind (fun a => doubleInl (T := T) (f a)) := by
  induction p with
  | pure a => rfl
  | vis e k ih =>
    exact congrArg (Prog.vis (S := S ⊕ₛ T) (A := B) (Sum.inl e)) (funext fun r =>
      congrArg (Prog.vis (S := S ⊕ₛ T) (A := B) (Sum.inl e)) (funext fun _ => ih r))

/-- And it is injective, so L26 does not separate it either. Recorded
so the ledger entry is exhaustive about which of the stated laws the
adversary survives: L25, L26, and every law about `Handler.sum`. -/
theorem doubleInl_injective {S T : Sig} {A : Type u} :
    ∀ (p q : Prog S A), doubleInl (T := T) p = doubleInl (T := T) q → p = q := by
  intro p
  induction p with
  | pure a =>
    intro q hq
    cases q with
    | pure b => simpa [doubleInl] using hq
    | vis e' k' => simp [doubleInl] at hq
  | vis e k ih =>
    intro q hq
    cases q with
    | pure b => simp [doubleInl] at hq
    | vis e' k' =>
      have hq' : Prog.vis (S := S ⊕ₛ T) (Sum.inl e)
                   (fun r => Prog.vis (S := S ⊕ₛ T) (Sum.inl e)
                     (fun _ => doubleInl (T := T) (k r)))
               = Prog.vis (S := S ⊕ₛ T) (Sum.inl e')
                   (fun r => Prog.vis (S := S ⊕ₛ T) (Sum.inl e')
                     (fun _ => doubleInl (T := T) (k' r))) := hq
      injection hq' with he hk
      injection he with he'
      subst he'
      refine congrArg (Prog.vis e) (funext fun r => ih r (k' r) ?_)
      injection congrFun (eq_of_heq hk) r with _ h2
      exact congrFun h2 r

/-! #### Why L25 and L26 cannot see it — the adversary FACTORS

The structural account of the break, adopted from the breaker:
`contracts/attacks/PDD-7/Attack.lean` §3 @ `b509cb20`. The packet's
closing paragraph stated this as a lesson; the breaker made it a
theorem, and the generalization is what makes it worth keeping.

`doubleInl` is the real injection precomposed with a monad-morphism
ENDOMORPHISM of `Prog S`. L25 and L26 are closed under precomposition
with any such endomorphism, so they are blind to the whole family
`Prog.inl ∘ φ` and not merely to this one member. Any future law meant
to exclude a performs-too-much or performs-too-little implementation
inherits the same limitation, and needs an observation rather than an
equation between programs. -/

/-- The doubling endomorphism, inside one signature. -/
def dup {S : Sig} {A : Type u} : Prog S A → Prog S A
  | .pure a => .pure a
  | .vis e k => .vis e fun r => .vis e fun _ => dup (k r)

theorem dup_bind {S : Sig} {A B : Type u} (p : Prog S A) (f : A → Prog S B) :
    dup (p.bind f) = (dup p).bind (fun a => dup (f a)) := by
  induction p with
  | pure a => rfl
  | vis e k ih =>
    exact congrArg (Prog.vis (S := S) (A := B) e) (funext fun r =>
      congrArg (Prog.vis (S := S) (A := B) e) (funext fun _ => ih r))

theorem dup_injective {S : Sig} {A : Type u} :
    ∀ (p q : Prog S A), dup p = dup q → p = q := by
  intro p
  induction p with
  | pure a =>
    intro q hq
    cases q with
    | pure b => simpa [dup] using hq
    | vis e' k' => simp [dup] at hq
  | vis e k ih =>
    intro q hq
    cases q with
    | pure b => simp [dup] at hq
    | vis e' k' =>
      have hq' : Prog.vis (S := S) e (fun r => Prog.vis (S := S) e (fun _ => dup (k r)))
               = Prog.vis (S := S) e' (fun r => Prog.vis (S := S) e' (fun _ => dup (k' r))) := hq
      injection hq' with he hk
      subst he
      refine congrArg (Prog.vis e) (funext fun r => ih r (k' r) ?_)
      injection congrFun (eq_of_heq hk) r with _ h2
      exact congrFun h2 r

/-- **The structural explanation of the break.** Breaker's, adopted. -/
theorem doubleInl_factors {S T : Sig} {A : Type u} (p : Prog S A) :
    doubleInl (T := T) p = Prog.inl (dup p) := by
  induction p with
  | pure a => rfl
  | vis e k ih =>
    exact congrArg (Prog.vis (S := S ⊕ₛ T) (A := A) (Sum.inl e)) (funext fun r =>
      congrArg (Prog.vis (S := S ⊕ₛ T) (A := A) (Sum.inl e)) (funext fun _ => ih r))

/-- L25 for the adversary, re-derived from the factorization with no
induction over the adversary at all — which is the point: the law is
inherited, so it cannot discriminate. -/
theorem doubleInl_bind' {S T : Sig} {A B : Type u} (p : Prog S A) (f : A → Prog S B) :
    doubleInl (T := T) (p.bind f)
      = (doubleInl (T := T) p).bind (fun a => doubleInl (T := T) (f a)) := by
  simp only [doubleInl_factors, dup_bind, Prog.inl_bind]

/-- L26 for the adversary, likewise inherited. -/
theorem doubleInl_injective' {S T : Sig} {A : Type u} (p q : Prog S A)
    (h : doubleInl (T := T) p = doubleInl (T := T) q) : p = q :=
  dup_injective p q (Prog.inl_injective (T := T) _ _
    (by rw [← doubleInl_factors, ← doubleInl_factors]; exact h))

/-! #### The honest constraint on L23's quantifier — `Id` is not enough

Breaker's NOTE-1, adopted (`Attack.lean` §2 @ `b509cb20`). The packet's
first draft justified L23's wide quantifier with a claim about `RefM`
that neither side has proved. This is the version that IS proved, and
it is a lower bound rather than a characterization: a separating target
must RECORD effects. `Id` does not, and narrowing ADQ-INL to it makes
the law FALSE. -/

theorem doubleInl_interpret_inl_Id {S T : Sig}
    (h : Handler S Id) (g : Handler T Id) {A : Type} (p : Prog S A) :
    interpret (h.sum g) (doubleInl (T := T) p) = interpret h p := by
  induction p with
  | pure a => rfl
  | vis e k ih => exact ih (h.handle e)

/-- Narrowing ADQ-INL's target quantifier to `Id` makes it FALSE. -/
theorem narrowing_to_Id_fails :
    ¬ (∀ (S T : Sig) (ι : {A : Type} → Prog S A → Prog (S ⊕ₛ T) A),
        (∀ (h : Handler S Id) (g : Handler T Id) {A : Type} (p : Prog S A),
           interpret (h.sum g) (ι p) = interpret h p) →
        ∀ {A : Type} (p : Prog S A), ι p = Prog.inl p) := by
  intro hyp
  have hEq := hyp TickSig TickSig (fun {_} p => doubleInl p)
    (fun h g {_} p => doubleInl_interpret_inl_Id h g p) tick
  have hc := congrArg
    (fun x => (interpret (tickHandler.sum tickHandler) x) 0) hEq
  rw [doubleInl_tick_count, inl_tick_count] at hc
  have h2 : (2 : Nat) = 1 := congrArg Prod.snd hc
  omega

/-! ### Adversary 4 — the oracle-discarding `handleLlm`

Breaker's HOLE-2 witness, adopted into the castle so the boundary
cannot be relaxed without a red build
(`contracts/attacks/PDD-7/Attack.lean` §5 @ `b509cb20`).

This one attacks a LAW OF THIS PACKET rather than a definition of the
library, and it is the only adversary here that found a real gap: L31
was described as a client guarantee and is not one. -/

/-- An adversarial `handleLlm` that IGNORES the oracle and answers
every inference with the empty string. -/
def badHandleLlm (oracle : String → String) : Prog AgentSig A → Prog CasSig A
  | .pure a => .pure a
  | .vis (Sum.inl e) k => .vis e (fun r => badHandleLlm oracle (k r))
  | .vis (Sum.inr (LlmE.infer _)) k => badHandleLlm oracle (k "")

/-- The adversary satisfies **L31 in full**, at every universe — so L31
pins nothing outside `Prog.inl`'s image. -/
theorem badHandleLlm_liftCas (oracle : String → String) {A : Type u}
    (p : Prog CasSig A) : badHandleLlm oracle (liftCas p) = p := by
  induction p with
  | pure a => rfl
  | vis e k ih => exact congrArg (Prog.vis e) (funext ih)

def wildOracle : String → String := fun s => s ++ "!"

theorem badHandleLlm_differs :
    badHandleLlm wildOracle (infer "x") ≠ Prog.handleLlm wildOracle (infer "x") := by
  intro h
  have h1 : (Prog.pure "" : Prog CasSig String) = Prog.pure "x!" := h
  injection h1 with h2
  exact absurd h2 (by decide)

/-- **L30 is what kills it.** The law a `runAgent` client must cite for
an oracle guarantee is L30, never L31 alone. -/
theorem badHandleLlm_not_interpret :
    badHandleLlm wildOracle (infer "x")
      ≠ interpret (idHandler.sum (llmOracleHandler wildOracle)) (infer "x") := by
  rw [← handleLlm_eq_interpret]
  exact badHandleLlm_differs

end Adversary

/-! ## Axiom census

Printed at build time so the claim is read off the run rather than
asserted in a document. The two axioms this module may use are
`propext` and `Quot.sound`; anything else — in particular `sorryAx` or
`Classical.choice` — is a finding, and this file is where it would
show.

**`funext` is not on that list, and cannot be** (breaker's NOTE-4,
`contracts/attacks/PDD-7/` @ `b509cb20`). An earlier version of this
note named "`propext`, `funext` and `Quot.sound`" as the three the
census watches for. In Lean 4 `funext` is a THEOREM derived from
`Quot.sound`, not an axiom, so it can never appear in a
`#print axioms` output. The instrument was sound; the prose named a
watch-item the instrument cannot report, which would have let a reader
mistake its absence for evidence. The heavy use of `funext` throughout
this module is accounted for by the `Quot.sound` entries. -/

#print axioms Prog.op_bind
#print axioms failWith_bind
#print axioms Handler.sum_unique
#print axioms interpret_inl
#print axioms interpret_inr
#print axioms Prog.inl_bind
#print axioms Prog.inl_injective
#print axioms inl_unique_one_target
#print axioms Prog.inl_unique
#print axioms inr_unique_one_target
#print axioms Prog.inr_unique
#print axioms llmOracleHandler_unique_one_program
#print axioms llmOracleHandler_unique
#print axioms handleLlm_bind
#print axioms handleLlm_eq_interpret_fun
#print axioms handleLlm_liftCas
#print axioms handleLlm_liftCas_via_laws
#print axioms Adversary.doubleInl_not_interpret_inl
#print axioms Adversary.doubleInl_bind
#print axioms Adversary.doubleInl_factors
#print axioms Adversary.narrowing_to_Id_fails
#print axioms Adversary.badHandleLlm_liftCas
#print axioms Adversary.badHandleLlm_not_interpret
#print axioms Adversary.badAgentSum_not_interpret_inr
#print axioms Adversary.swapSum_not_sum_handle_inl

end Cas.Lang
