# PDD-7 — the breaker's verdict

Adversarial record against the PDD-7 contract packet
(`library/cas/contracts/PDD-7.contract.md`) and the castle it specifies
(`library/cas/Cas/Backend/SumAlgebra.lean`). The machine-checked half is
`Attack.lean` beside this file.

```
BREAKER    independent; did not build this castle
CASTLE     d714ef14  PDD-7: correct the exhibits finding — gitignored,
                     not absent; and they agree
  module   03ca1435  PDD-7: the sum algebra proved — and L23 alone is
                     what pins the injection
  packet   8e7fe66a  PDD-7: the contract packet — the sum algebra,
                     stated before it is proved
  ledger   c2686dc6  PDD-7: the break ledger — L25 excludes nothing
  merge    7a3d558d  main into the branch (the exhibits arrive)
ATTACK     contracts/attacks/PDD-7/Attack.lean
BRANCH     attack/opus-cc-mac/pdd-7
```

# VERDICT — **STANDS** (2 HOLEs, 6 NOTEs; no BREAK)

No theorem in `SumAlgebra.lean` is false. Every gate reproduces to the
byte. The packet's own break ledger is CONFIRMED in both directions,
re-elaborated here by a route the castle does not use. Nothing is
irreproducible and no axiom is smuggled.

What is found is a gap between the packet's PROSE and its theorems in
two places, both claim-scope: the target quantifier the packet declares
load-bearing is not, and the one law the packet presents as a standalone
client guarantee admits a wrong-but-passing implementation.

---

## §1 — Gates, reproduced

Run from `library/cas` at `d714ef14`, clean tree.

```
lake --wfail build Cas CasBackend CasExamples CasWp
  → Build completed successfully (95 jobs).
  → ℹ [57/95] Built Cas.Backend.SumAlgebra (1.2s)      [in the job list]

mise run check:cas
  → exit 0; every byte gate ok. Unmoved, to the byte:
      surface/cas-surface.json      955041 bytes — 2026 declarations
      surface/cas-obligations.json   17363 bytes — 68 obligations
      surface/cas-laws.json           9825 bytes — 9 of 37 rulings bound
      REGISTRY.md                    14529 bytes — 11 sorts
      ../../docs/lab-core/ENVIRONMENT.json 37002 bytes — 45 tasks
    (all 40 emitted artifacts `ok`; the three supportInterpreter ledgers
     confirm the module is outside `Walk.libraryImports`.)

git status → clean
```

### Sorry-control, repeated by this hand

`SumAlgebra.lean:114-115`, `Prog.op_bind`'s `:= rfl` replaced by
`:= by sorry`:

```
warning: Cas/Backend/SumAlgebra.lean:114:8: declaration uses `sorry`
info:    'Cas.Lang.Prog.op_bind' depends on axioms: [sorryAx]
error: build failed                                        [exit 1]
```

Reverted (`git checkout --`), rebuilt: `Build completed successfully
(95 jobs)`, exit 0. **Both signals fire** — `--wfail` promotes the
warning, and the module's own census independently reports `sorryAx`.
The control is real, not decorative.

### Axiom census — independent, over ALL declarations

The module prints `#print axioms` for 16 headline declarations. This
census walks the compiled environment for every constant whose defining
module is `Cas.Backend.SumAlgebra`, drops compiler-generated names by
`Walk.isGenerated`'s own suffix list, and calls `Lean.collectAxioms` on
each — definitions included, not only theorems.

```
PUBLIC COUNT  = 52          ← the packet claims 52; exact match
PRIVATE COUNT =  3          ← handler_eq_of_handle
                              + 2 generated match-splitters
AXIOM UNION over all 55 = [Quot.sound, propext]
```

`Cas.Lang.Prog.op_bind :: []` — axiom-free, as claimed. No `sorryAx`,
no `Classical.choice`, nothing else. **The packet's census claim
reproduces in full**, and over a strictly larger declaration set than
the module prints.

### Commit order — packet first

```
8e7fe66a  A  library/cas/contracts/PDD-7.contract.md
03ca1435  A  library/cas/Cas/Backend/SumAlgebra.lean
```

The packet was added two commits before the module existed. Order
**correct**; the breaker's discipline was kept.

---

## §2 — HOLE-1: the target quantifier is not load-bearing

**Attacked.** `contracts/PDD-7.contract.md:399-407` (NOTE ADQ-INL) and
`Cas/Backend/SumAlgebra.lean:54-59`:

> The load-bearing detail in `Prog.inl_unique` is the quantification
> over EVERY target monad. It is not generality for its own sake …
> The refutation of the doubling injection is carried out at a handler
> into `StateT Nat Id` for exactly that reason.

and

> The strength is also not an accident of convenience. … Weakening the
> quantifier to `RefM` would make the law exactly as blind as the word
> gate.

**Witness — the quantifier can be narrowed to ONE monad and ONE handler
pair, and the conclusion survives** (`Attack.lean` §2):

```lean
theorem inl_unique_one_target {S T : Sig}
    (ι : {A : Type} → Prog S A → Prog (S ⊕ₛ T) A)
    (hι : ∀ {A : Type} (p : Prog S A),
        interpret ((inlHandler S T).sum (inrHandler S T)) (ι p)
          = interpret (inlHandler S T) p)
    {A : Type} (p : Prog S A) : ι p = Prog.inl p
```

This is strictly stronger than `Prog.inl_unique`: same conclusion from a
hypothesis at a single instance of the castle's ∀. And
`syntactic_hyp_iff` shows why — that instance of the hypothesis is
EQUIVALENT to the conclusion, by exactly the two rewrites
(`sum_inlHandler_inrHandler`, `interpret_id`, `interpret_inlHandler`)
that `Prog.inl_unique`'s proof performs. The counting target
`StateT Nat Id` is never used in `Prog.inl_unique`. The theorem is
carried entirely by the INITIAL monad.

`inl_unique_via_initiality` closes the second door: the alternative
route through `eq_of_forall_interpret` plus ADQ-SUM reaches the same
conclusion and bottoms out at the same instance, because
`eq_of_forall_interpret` is itself `interpret_id` at `idHandler`
(`Representation.lean:83-84`).

**Why this is a HOLE and not a BREAK.** `Prog.inl_unique` is true. What
is wrong is the packet's account of what makes it true, and the account
is operative: it instructs a later hand that the wide quantifier must
not be weakened. The real constraint is different — NOTE-1.

**The RefM half of the claim is unproved on both sides.** The packet's
justification for the wide quantifier is that a law stated at `RefM`
would be word-blind; the packet's own claim-scope
(`contract.md:481-490`) declines to prove
`ObsEq H (liftCas p) (doubleInl p)`. So the stated reason for the
quantifier rests on an assertion the same document withholds. This
breaker did not close it either (§7, failed attempt 6) — it is recorded
as open, not refuted.

---

## §3 — HOLE-2: L31 is wrong-but-passing on its own

**Attacked.** `contract.md:320-328` (LAW L31) and
`SumAlgebra.lean:404-413`, whose docstring reads *"The law every
`runAgent` client assumes."*

**Witness** (`Attack.lean` §5, kernel-checked, no `sorry`):

```lean
def badHandleLlm (oracle : String → String) : Prog AgentSig A → Prog CasSig A
  | .pure a => .pure a
  | .vis (Sum.inl e) k => .vis e (fun r => badHandleLlm oracle (k r))
  | .vis (Sum.inr (LlmE.infer _)) k => badHandleLlm oracle (k "")

theorem badHandleLlm_liftCas (oracle) {A : Type u} (p : Prog CasSig A) :
    badHandleLlm oracle (liftCas p) = p          -- L31, in full
theorem badHandleLlm_differs :
    badHandleLlm wildOracle (infer "x") ≠ Prog.handleLlm wildOracle (infer "x")
theorem badHandleLlm_not_interpret :
    badHandleLlm wildOracle (infer "x")
      ≠ interpret (idHandler.sum (llmOracleHandler wildOracle)) (infer "x")
```

The adversary DISCARDS THE ORACLE ENTIRELY and satisfies L31 at every
universe, by the same induction the real one uses — because `liftCas p`
contains no `infer` node, so L31 pins nothing outside `Prog.inl`'s image.
A `runAgent` client leaning on L31 alone has no oracle guarantee at all.

**L30 is what kills it**, and L30 is in the packet — so the law SET is
adequate. What is missing is the boundary line. The packet's claim-scope
section covers L27/L28/L29/L32 and the universe restriction on L30, and
never says that L31's reach stops at the `liftCas` image. The same shape
as HOLE-1: the theorem is right, the prose around it is not.

---

## §4 — The ledger row: CONFIRMED, both directions

The packet's Breaks row (`contract.md:604-666`) claims THE-ALGEBRA
§3.2's *"KILLED BY interpret_inl (L23) together with `inl` is a monad
morphism (L25); nothing weaker separates them"* is false in both halves.
Re-elaborated here **by a route the castle does not use**, so the
confirmation is not a re-run of the castle's own tactics.

**The route: `doubleInl` FACTORS.**

```lean
def dup {S : Sig} {A : Type u} : Prog S A → Prog S A
  | .pure a => .pure a
  | .vis e k => .vis e fun r => .vis e fun _ => dup (k r)

theorem doubleInl_factors (p : Prog S A) :
    Adversary.doubleInl (T := T) p = Prog.inl (dup p)
```

From which, with no new induction over the adversary:

- `doubleInl_bind'` := `doubleInl_factors` + `dup_bind` + `Prog.inl_bind`
- `doubleInl_injective'` := `doubleInl_factors` + `Prog.inl_injective`
  + `dup_injective`
- `doubleInl_pure'` := `rfl`

**Half (b) — "L25 supplies what is missing" is FALSE.** Confirmed. The
adversary satisfies L25 and L26 for a structural reason the packet
states as a lesson but does not prove: `doubleInl` is the real injection
precomposed with a monad-morphism ENDOMORPHISM of `Prog S`, and L25/L26
are closed under precomposition with any such endomorphism. Every
equation-between-programs law is blind to that whole family, not just to
this one member.

**Half (a) — "L23 alone does not suffice" is FALSE.** Confirmed, and
stated as a theorem rather than as an inference from `Prog.inl_unique`:

```lean
theorem doubleInl_fails_L23_premise :
    ¬ (∀ (M : Type → Type) [Monad M] [LawfulMonad M]
         (h g : Handler Adversary.TickSig M) {A : Type}
         (p : Prog Adversary.TickSig A),
         interpret (h.sum g) (Adversary.doubleInl p) = interpret h p)
```

by `Prog.inl_unique` applied to `doubleInl` against the witness
`doubleInl_tick_ne`. L23 at every lawful target kills the adversary with
no appeal to L25 or L26.

**The confirmation is confirmed.**

---

## §5 — Fresh adversaries: three of this breaker's own, plus one

Every discriminating observation is a HANDLER, per the castle's own
finding that the word gate cannot see operation counts. No adversary
escaped.

| # | adversary | what it does | killed by |
|---|---|---|---|
| A1 | `swapTwoInl` | REORDERS the first two operations | **L23** (`swapTwoInl_not_interpret_inl`, order-recording handler into `StateT (List Bool) Id`) **and L25** (`swapTwoInl_not_monad_morphism`) |
| A2 | `dropInl` | ELIDES the first operation, whose answer is `Unit` and provably unused | **L23** (`dropInl_not_interpret_inl`) **and L26** (`dropInl_not_injective`: it collapses `opT true` and `opT false`) |
| A3 | `putDoubleInl` | doubles ONLY the `put` tag, at `CasSig` itself | **L23** (`putDoubleInl_not_interpret_inl`, at `StateT Nat (Except Unit)`) |
| A4 | `badHandleLlm` | discards the oracle | **L30**; **NOT L31** — that is HOLE-2 |

**No HOLE among them.** A1 and A2 are killed twice over, which is the
sharpening in NOTE-3: L25 and L26 are not idle laws, they are idle
against `doubleInl` specifically. A3 is the interesting one — it is
tag-selective, so `putDoubleInl_load_agrees` proves that the very
handler which separates it on a `put` cannot see it on a `load`. That is
the finest-grained defect the law set still catches.

An adversary that escapes is impossible for the stated type: ADQ-INL is
categorical, so every `ι : {A : Type} → Prog S A → Prog (S ⊕ₛ T) A`
either fails L23 at some lawful target or IS `Prog.inl`.

---

## §6 — `handleLlm`: the oracle quantifier, and the asserted bind law

**The quantifier reaches every function and nothing else.** L30/L31
quantify over `oracle : String → String` — total, deterministic, pure.
Any such function is covered, including ones with no algorithm: the
statements are ∀-quantified and both inductions are on `p`, never on the
oracle. Mechanically: `handleLlm_liftCas` depends on `[Quot.sound]` and
nothing more — no `Classical.choice` enters.

**What the quantifier cannot reach is a nondeterministic or stateful
oracle, and the type is what forbids it.**

```lean
theorem askTwice_answers_agree (oracle) (a b : String)
    (h : askTwice.handleLlm oracle = Prog.pure (a, b)) : a = b
```

Two identical prompts in one program ALWAYS get the same answer, by
theorem, for every oracle in the quantifier. A history-dependent oracle
would be a `Handler LlmSig M` for state-carrying `M`, and then
`interpret (idHandler.sum g)` lands in `M`, not in `Prog CasSig` —
`handleLlm`'s codomain rules it out. `Interp.lean:21-22`'s *"the
oracle's nondeterminism enters only as the recorded answer"* is a
modelling stipulation the type enforces, not a theorem about oracles.
Recorded here because the packet's claim-scope does not state it.

**Claim-scope check against `Interp.lean:19,181-183` — NO dependency.**
There is no declaration named `bind_law` anywhere in `library/cas` or
`.staging` (grep). The assertion at those lines is PROSE — the docstring
claim that `handleLlm` *"interprets by monad morphism"*. There is
nothing for a PDD-7 theorem to depend on, and the census over all 55
declarations of the module is `{propext, Quot.sound}`.

The dependence runs the other way. `Attack.lean` §5:

```lean
theorem handleLlm_bind (oracle) {A B : Type} (p : Prog AgentSig A)
    (f : A → Prog AgentSig B) :
    (p.bind f).handleLlm oracle
      = (p.handleLlm oracle).bind (fun a => (f a).handleLlm oracle) := by
  simp only [handleLlm_eq_interpret]
  exact interpret_bind (idHandler.sum (llmOracleHandler oracle)) p f
```

Two lines, from PDD-7's own L30 plus core `interpret_bind` at the
shipped `LawfulMonad (Prog S)` (`Representation.lean:54`). **PDD-7
discharges PDD-8's boundary finding rather than depending on it**, and
the packet's "Not claimed: L32 … the corollary is not stated, so the row
stays OWED" understates what it already has.

---

## §7 — The remaining NOTEs

**NOTE-1 — the honest constraint on the quantifier: `Id` is not enough.**
`doubleInl_interpret_inl_Id` proves the doubling injection satisfies L23
at EVERY handler pair into `Id`, so `narrowing_to_Id_fails` proves
ADQ-INL becomes FALSE under that narrowing. Combined with HOLE-1: the
quantifier must reach a target that RECORDS effects — the initial monad
suffices, `Id` does not — which is a sharper and provable version of the
claim the packet makes.

**NOTE-2 — the advertised counting target does not exist at the store
language.**

```lean
theorem no_Id_counter_for_CasSig (h : Handler CasSig (StateT Nat Id)) : False :=
  ((h.handle (CasE.fail "x")) 0).1.elim
```

`CasE.fail` answers `Empty` and `Id` has no branch to put it in, so
`Handler CasSig (StateT Nat Id)` is UNINHABITED. The module docstring's
recipe — *"a target monad where an operation is visible: `StateT Nat
Id`"* — is available only at the toy `TickSig`. The castle's refutation
is sound (it refutes a ∀-statement, witnessed anywhere), but a reader
carrying the recipe to `CasSig` finds it does not typecheck. A3 above
had to use `StateT Nat (Except Unit)`; that substitution is the fix.

**NOTE-3 — "L25 excludes THE ADVERSARY from nothing" is right; "L25
excludes nothing" would not be.** The module's heading *"What L25
contributes to killing it — nothing"* is accurate as scoped. A1 and A2
above are killed by L25 and L26 respectively, so those laws earn their
place; `doubleInl_factors` is the precise account of the family they
cannot see.

**NOTE-4 — ADQ-SUM's premises are exactly L21+L22, no smuggling; and
the census cannot report `funext`.** `sum_unique_iff` upgrades
`Handler.sum_unique` to an equivalence — the premises are exactly L21
and L22 at `k`, with nothing else assumed — and
`sum_unique_needs_right_premise` / `sum_unique_needs_left_premise` show
that neither premise is spare.
The only machinery is structure eta plus `funext`, which is
`Handler.ext`-equivalent and nothing beyond it. Consistent with the
census line `Handler.sum_unique … [Quot.sound]`: in Lean 4 `funext` is a
THEOREM derived from `Quot.sound`, not an axiom. Consequence for the
module tail (`SumAlgebra.lean:669-675`), which names *"`propext`,
`funext` and `Quot.sound`"* as "the estate's clean three" the census
watches for: `funext` can never appear in a `#print axioms` output. The
instrument is sound; the prose names a watch-item it cannot report.

**NOTE-5 — the categoricity does not reach the universes `liftCas` is
typed at.** Read off `Attack.lean` §7's `#check` block:

```
@liftCas             : {A : Type u_1} → Prog CasSig A → Prog AgentSig A
@Prog.handleLlm      : {A : Type u_1} → …
@handleLlm_liftCas   : ∀ … {A : Type u_1} …
@Prog.inl_unique     : ∀ … (ι : {A : Type} → …) …          ← Type 0 only
@handleLlm_eq_interpret : ∀ … {A : Type} …                 ← Type 0 only
```

The packet discloses the `Type` restriction for L30 and not for ADQ-INL.
Unexploitable in practice — no Lean definition can branch on universe
level — but as stated, the categoricity pins `Prog.inl` at `Type 0` only
while the shipped `liftCas` is universe-polymorphic.

**NOTE-6 — four results the packet could have had.** Offered, not
demanded: `inl_unique_one_target` (a strictly stronger ADQ-INL);
`llmOracleHandler_unique` (**ADQ-L30**, which the packet never states —
L30 alone does not say `llmOracleHandler oracle` is the ONLY handler
making `handleLlm` an interpretation; it is, and the proof is six
lines); `handleLlm_bind` (L32); `doubleInl_factors` (the structural
account of the break, which generalizes the packet's own closing
paragraph from a lesson into a theorem).

---

## §8 — Failed break attempts, kept as record

1. **Narrow ADQ-INL to the initial monad and break it.** FAILED — the
   narrowed law is TRUE (`inl_unique_one_target`). The failure IS
   HOLE-1: the hypothesis was over-strong, not the theorem wrong.
2. **Escape the counting refutation by claiming the target is not
   lawful.** FAILED, mechanically:
   `example : LawfulMonad Adversary.Counter := inferInstance`, likewise
   `CCounter` and `Prog CasSig` (§6 of `Attack.lean`).
3. **Show ADQ-INL vacuous** — the standard attack on a uniqueness
   theorem with a strong premise. FAILED: the premise is inhabited by
   `interpret_inl`, which holds at a BARE `Monad`, weaker than the
   premise asks. Elaborated in §1 and §6, not taken from the packet's
   assertion.
4. **Build the tag-selective `CasSig` adversary at the castle's
   advertised `StateT Nat Id`.** FAILED, and necessarily — that handler
   type is uninhabited. Became NOTE-2; the adversary was rebuilt at
   `StateT Nat (Except Unit)`.
5. **Find an injection no law kills.** FAILED, and provably impossible
   for the stated type: ADQ-INL is categorical.
6. **Close `ObsEq H (liftCas p) (putDoubleInl p)`** — the packet's own
   open item and the ground of its "weakening to `RefM` would be blind"
   claim. NOT COMPLETED. It needs `Cas.put` idempotence and `load`
   purity lemmas this slice does not carry, exactly as the packet's
   claim-scope says. Recorded so the RefM half of HOLE-1 is read as
   OPEN on both sides, not as refuted.

---

## §9 — Close conditions

**HOLE-1** closes when the packet's NOTE ADQ-INL and the module's
docstring §"What the file establishes" say what is true: the target
quantifier must reach a target that records effects, `Id` does not, the
INITIAL monad suffices and is what the proof uses, and the counting
handler is the refutation's device rather than the categoricity's. If
`inl_unique_one_target` is adopted, `Prog.inl_unique` becomes its
corollary and the prose has nothing left to overstate.

**HOLE-2** closes when L31's row and `handleLlm_liftCas`'s docstring
record that L31 constrains only `Prog.inl`'s image, and that L30 is the
law a `runAgent` client must cite for an oracle guarantee.
`badHandleLlm` should move into the castle's `Adversary` namespace
beside the other three, so the boundary cannot be relaxed without a red
build.

Neither hole requires a theorem to change. Both are prose against
kernel-checked fact, which is the class the packet itself named
`claim-scope` and the class its own break row fell in.

---

# RE-RUN 2026-08-30 — against `e1ceb205`

## STATUS — **STANDS-AMENDED. Both holes CLOSED.**

```
AMENDED  e1ceb205  module fixes for both holes, eight results adopted
PACKET   ac3a0ece  packet amendments for the breaker's two holes
RECORD   AttackAmended.lean beside this file
```

`Attack.lean` is **unedited** and stays the record against `d714ef14`.
It also still elaborates clean against `e1ceb205` (exit 0, zero errors,
every name resolving to `PDD7Attack.*`) — expected, and worth saying
because PDD-1's breaker mispredicted the same thing: those theorems are
about the law set as it stood, and EXTENDING a law set cannot falsify a
theorem about the old one. The close conditions are the ones §9 named,
and they are discharged below.

## Gates on the amended module — re-run by this hand

```
lake --wfail build Cas CasBackend CasExamples CasWp
  Build completed successfully (95 jobs).          [exit 0]
  ℹ [94/95] Built Cas.Backend.SumAlgebra (1.9s)

mise run check:cas                                 [exit 0]
  surface/cas-surface.json      955041 bytes — 2026 declarations
  surface/cas-obligations.json   17363 bytes — 68 obligations
  surface/cas-laws.json           9825 bytes — 9 of 37 bound
  REGISTRY.md                    14529 bytes
  ../../docs/lab-core/ENVIRONMENT.json 37002 bytes
  every byte gate ok; UNMOVED to the byte from the first pass, so the
  371-line module change is still outside Walk.libraryImports.

CENSUS (independent env walk, all constants of the module)
  PUBLIC COUNT  = 69       (was 52; +17 for the eight adopted results
                            and their supporting definitions)
  PRIVATE COUNT =  3       (unchanged: handler_eq_of_handle + 2
                            generated match-splitters)
  AXIOM UNION over all 72 = [Quot.sound, propext]
  Cas.Lang.Prog.op_bind :: []            still axiom-free
  no sorryAx, no Classical.choice
```

**Sorry-control, re-run at the NEW primary theorem.** `syntactic_hyp_iff`'s
proof replaced by `sorry`:

```
warning: Cas/Backend/SumAlgebra.lean:377:8: declaration uses `sorry`
info:  'Cas.Lang.inl_unique_one_target' depends on axioms: [sorryAx]
info:  'Cas.Lang.Prog.inl_unique'       depends on axioms: [propext, sorryAx, Quot.sound]
error: build failed                                        [exit 1]
```

Reverted, rebuilt: 95 jobs, exit 0. The poison reaching **both**
`inl_unique_one_target` and `Prog.inl_unique` is itself the evidence for
HOLE-1's closure — see below.

## HOLE-1 — **CLOSED**, and structurally

Three independent checks, none of them a reading of prose.

1. **The proof term.** `AttackAmended.lean` §A prints it:

```lean
theorem Cas.Lang.Prog.inl_unique … :=
fun {S T} ι hι {A} p =>
  inl_unique_one_target (fun {A} => ι)
    (fun {x} q => hι (Prog (S ⊕ₛ T)) (inlHandler S T) (inrHandler S T) q) p

theorem Cas.Lang.inl_unique_one_target … :=
fun {S T} ι hι {A} p => (syntactic_hyp_iff (fun {A} => ι) p).mp (hι p)
```

The ∀-quantified form is now literally an application of the narrowed
one, which is literally the `.mp` of the iff. Not a docstring reorder.

2. **The axiom trace.** The planted `sorry` in `syntactic_hyp_iff`
propagates to `Prog.inl_unique`. A cosmetic fix that kept the old `rwa`
block would not have.

3. **The prose.** Every withdrawn claim is gone from both surfaces. The
module head carries a "What makes the categoricity work — corrected"
section (`SumAlgebra.lean:57-83`) and the packet's NOTE ADQ-INL
(`contract.md:437-476`) says the wide quantifier is generality and not
mechanism, that the counting target never enters the categoricity, and
that the `RefM`/word-gate comparison is **OPEN in both directions** —
naming both that the packet declined it and that this breaker failed to
close it (attack record §8, failed attempt 6). Nothing now claims what
nothing proves.

`inl_unique_factors_through_one_target` re-derives the factoring in this
record so it is not held on the castle's word alone.

## HOLE-2 — **CLOSED**, and build-enforced

L31's reach line is present in **both** required places: the packet row
(`contract.md:329-347`, NOTE L31) and the docstring
(`SumAlgebra.lean:522-530`). Both say the same three things — L31
constrains `handleLlm` only on `Prog.inl`'s image, `badHandleLlm`
satisfies it at every universe, and a client wanting an oracle guarantee
must cite **L30**.

The stronger half: `badHandleLlm` is now `Cas.Lang.Adversary.badHandleLlm`
with `badHandleLlm_liftCas` and `badHandleLlm_not_interpret` beside it,
both re-elaborated in §A. Relaxing the boundary back now means deleting
a theorem, which is a red build rather than a prose edit — exactly the
close condition §9 asked for.

## Adopted results — re-elaborated, and the credits

All eight discharged in `AttackAmended.lean` §B: each of this record's
ORIGINAL statements is inhabited by the castle's adopted declaration, so
nothing was weakened on the way in. `dup_bind`, `dup_injective`,
`doubleInl_bind'` and `doubleInl_injective'` are checked as well as
`doubleInl_factors`, since the derived pair was the point.

**Credits verified, by path and commit, at every site.** The module head
carries the debt block (`SumAlgebra.lean:109-118`) naming
`library/cas/contracts/attacks/PDD-7/ @ b509cb20` and listing all eight;
each adopted declaration repeats it in its own docstring
(`contracts/attacks/PDD-7/Attack.lean` §2 / §3 / §5 @ `b509cb20`); the
packet carries the attack section (`contract.md:877-942`) with the
adoption table and the two RESULT blocks that ran in the packet's
favour. Correct and sufficient.

**ADQ-L30** (`contract.md:411-425`) is as this record supplied it, with
the packet's own line that it "omitted this row and should not have".
**L32** (`SumAlgebra.lean:498-515`) carries the cross-cite: the estate's
`Interp.lean:19,181-183` assertion is prose with no declaration behind
it, nothing in the slice depended on it, and `handleLlm_bind` supplies
what it was claiming — so PDD-7 discharges PDD-8's boundary rather than
depending on it. Both as supplied.

## NOTE-7 — the fresh probe: the correction reached ONE of three rows

**Does not block the landing. It is consistency, not correctness — no
claim is false, no theorem unsound, no adversary admitted.**

HOLE-1 was never a fact about `Prog.inl`. It was a fact about a PROOF
SHAPE: a categoricity whose hypothesis is ∀-quantified while its proof
consumes one instance, at which the hypothesis is equivalent to the
conclusion. The fix pass corrected the row this breaker pointed at and
left the identical shape standing in the two it did not.

- **`Prog.inr_unique`** keeps the original one-shot `rwa`; there is no
  `syntactic_hyp_iff_inr` and no `inr_unique_one_target`. Supplied here
  (`AttackAmended.lean` §C1), with `inr_unique_is_corollary` showing the
  restructure goes through on the right by the same two lines.
- **`llmOracleHandler_unique` — the ADQ-L30 row just adopted** — has the
  same shape. Its hypothesis ranges over every `A : Type` and every
  `p : Prog AgentSig A`; its proof consumes, per operation, exactly
  `A := String`, `p := .vis (.inr (.infer q)) .pure`. `l30_hyp_iff`
  proves that instance EQUIVALENT to the conclusion pointwise —
  `Prog.bind_pure_right` playing the role `interpret_id` plays on the
  left — and `llmOracleHandler_unique_one_program` is the strictly
  stronger row, with the shipped one as its corollary.

  **Partly this breaker's own doing**: the record supplied
  `llmOracleHandler_unique` in the ∀-form and did not narrow it. Named
  so the ledger is not tidier than the history.

`ADQ-SUM` is exempt and provably so: `sum_unique_iff` already established
its premises are pointwise-minimal. There is no fourth row.

**Close condition.** Adopt `syntactic_hyp_iff_inr`,
`inr_unique_one_target`, `l30_hyp_iff` and
`llmOracleHandler_unique_one_program` from `AttackAmended.lean` §C, with
`Prog.inr_unique` and `llmOracleHandler_unique` restated as their
corollaries. Four declarations, all written and kernel-checked here, so
folding them in is a copy. If the operator prefers to land PDD-7 now and
carry NOTE-7 as a follow-up, nothing is at risk — the shipped forms are
true and the ADQ block is adequate as it stands.

## On the declined adoption — `inl_unique_via_initiality`

**Concur with declining.** Its only content was that the second route
bottoms out at the same instance, and `syntactic_hyp_iff` now says that
in the module outright — so a third spelling of one theorem would cost
maintenance to record a finding the castle already carries; it stays
here as record.

## Re-run failed attempts

1. Break either closure — FAILED, both are mechanical (proof term, axiom
   propagation, castle-resident adversary).
2. Find a statement weakened in adoption — FAILED, all eight §B examples
   elaborate.
3. Find the `inr` asymmetry hiding an unsoundness — FAILED;
   `inr_unique_is_corollary` shows the restructure goes through.
4. Find a fourth categoricity row with the shape — FAILED, there is no
   fourth.
5. Close `ObsEq H (liftCas p) (doubleInl p)` — still not attempted to
   completion, and now correctly marked OPEN on both sides rather than
   gestured at.

## Verdict

```
HOLE-1   CLOSED
HOLE-2   CLOSED
NOTE-7   NEW, non-blocking (consistency); four fixes supplied
BREAK    none, either pass
STATUS   STANDS-AMENDED — PDD-7 lands on the operator's ruling
```
