# PDD-7 — the contract packet: the sum algebra and the carrier's missing monad laws

Ticket: `.staging/wave-2/PDD-7.md`. Process: `.claude/skills/implement/`
(SKILL.md, CONTRACT.md, IMPLEMENTER.md, BREAKER.md, CATALOG.md); lane
law `library/cas/AGENTS.md`. Owed-ledger item 2 of
`.staging/algebraic-review/THE-ALGEBRA.md` (§2.1, §2.3, §3.2).

Authored before `Cas/Backend/SumAlgebra.lean` exists and committed
ahead of it, so the git history carries the order (CONTRACT.md §The
pin).

```
CATEGORIES algebraic-laws, lemmas-proofs, contracts,
           abstraction-modules
```

CATALOG rows opened for those tags, and what each contributed:

- **§6.2 / §7.2 (`algebraic-laws`)** — unit, associativity and
  homomorphism are the shapes here, and the falsifier for each is an
  exhibited pair, not an argument. `Prog.inl` is claimed to be a monad
  MORPHISM, so §7.2's `UnaryToNat/Add` square (`h(op(x,y)) ≠
  op'(h x, h y)`) is the exact template for L25's falsifier.
- **§5.7 Mirror, the canonical trap (`algebraic-laws`)** — "a shallow
  involution can pass while the DEFINING equation fails; falsify the
  defining equation, not only the composite." This row is the whole
  reason this packet does not stop at L31. `handleLlm oracle (liftCas
  p) = p` is a composite round-trip; it is satisfied by injections
  that are wrong on the operation count, so the defining equations
  (L23, L25) are stated and attacked separately.
- **§8.0 / §8.3 the sorting trinity (`specification-design`, opened
  through `algebraic-laws`)** — a law set that is individually true
  and jointly too weak is the failure this process exists to catch.
  PDD-1's ledger fired exactly here. The analogue below is
  ADQ-SUM/ADQ-INL: the laws are stated, and then it is PROVED that
  nothing else satisfies them.
- **§9.2 / §9.4 / §9.5 (`abstraction-modules`)** — every public
  contract stated over the abstraction function, and each operation
  commuting with it. `Prog.inl` IS an abstraction function here (from
  `Prog S` into `Prog (S ⊕ₛ T)`), and §9.5's square is L23/L25.
  §9.4's "export the observation, not representation equality" is why
  L26 (injectivity) is stated at all — it is what licenses reading
  `p.inl = q.inl` as `p = q` at a client.
- **§5.1 / §5.2 (`lemmas-proofs`)** — no bodyless lemma; every
  statement below carries a kernel-checked body, and the wrong
  instantiation is the named risk (a lemma about `Prog.inl` invoked
  where `Prog.inr` sits).
- **§1.4 / §2.7 (`contracts`)** — the adequacy gap and the
  favorable-witness proof. Both adversaries below are §1.4's shape:
  a `c'` satisfying the stated contract while breaking the intent.
- **§B.7 / §B.8 (`proof-mechanics`, added by the breaker hand — the
  ticket did not tag it and the uniqueness theorems need it)** —
  universals proved for arbitrary, existentials discharged by
  exhibiting the witness. ADQ-INL is a universal over every target
  monad and every handler pair; the refutations are existentials with
  their witnesses in the tree.

## The degree claim

**I have shown algebraically that this can be implemented at the Lean
escalation tier**: every law below is a Lean statement over the
shipped `Prog`/`Sig`/`Handler` declarations (`Cas/Lang/Prog.lean:41-50`,
`Cas/Lang/Sig.lean:20-25`, `Cas/Lang/Handler.lean:63-66`,
`Cas/Lang/Interp.lean:184-187`, `Cas/Lang/Ops.lean:55-63`), proved to
the kernel with no `sorry`, no `native_decide`, and no new axiom; every
falsifier is a formal counter-`example` or a `¬ (∀ …)` theorem whose
witness the kernel evaluates.

The degree is higher than "each law proved", and the packet claims the
higher thing: for the two definitions the ticket says carry the whole
protection — `Handler.sum` and `Prog.inl`/`Prog.inr` — the law set is
proved CATEGORICAL. ADQ-SUM and ADQ-INL below say that any
implementation satisfying the stated laws IS the shipped one,
pointwise. That is the adequacy class discharged rather than argued,
in the shape PDD-2's `anchor_pins_wp` established for `wp`.

**The escalation gate is named, and it is a NEGATIVE gate.** This slice
adds theorems only, in a module outside `Walk.libraryImports`. Nothing
it proves reaches the host as new bytes, so `γ` is discharged by
byte-identity of every generated surface under `mise run check:cas` —
the claim is "the model gained theorems and the emitted TypeScript did
not move", and a red `--check` refutes it. There is no host battery
because there is no host change; per CONTRACT.md §Escalation this
packet's floor is the Lean statement plus the byte gate, written down
rather than implied.

## The module's home, and why it is not `Cas/Lang/`

Stated up front because a reader who goes looking for sum-algebra laws
will look in `Cas/Lang/` and not find them.

The theorem module lands at **`library/cas/Cas/Backend/SumAlgebra.lean`**
and its declarations live in `namespace Cas.Lang`, where their subjects
live. The path is forced by the ticket's fence ("no existing file
edited") against Lake's target graph:

- `[[lean_lib]] name = "Cas"` carries no `globs`, so it builds the root
  module `Cas` and its import closure and nothing else. A new
  `Cas/Lang/Sum.lean` that no module imports would be built by NO
  target — `lake --wfail build` would be green while never elaborating
  a line of it, and the ticket's gate would be vacuous.
- Getting it built means either editing `Cas/Lang/Lang.lean` to import
  it, or editing `lakefile.toml` to declare a library for it (PDD-2's
  device for `Cas.Lang.Wp`). Both edit an existing file. `lakefile.toml`
  is additionally the one file all three wave-2 castles would edit, so
  the fence is protecting a real collision, not a formality.
- `[[lean_lib]] name = "CasBackend"` carries `globs = ["Cas.Backend.+"]`
  and is in `defaultTargets` and in `check:cas`'s explicit build list.
  A new module under `Cas/Backend/` is therefore kernel-checked with
  zero edits. `Walk.libraryImports` (`tools/Walk.lean:45-56`) names the
  backend leaves INDIVIDUALLY, so a module not on that list is outside
  the surface, obligation and law ledgers and cannot move their bytes.

This is PDD-1's device, and PDD-9's ticket names it as the device to
use. `Cas/Backend/Canon.lean` is a pure theorem module living there for
exactly this reason. The cost is named rather than hidden: **the module
path says `Backend` and the module is not backend code.** Promoting it
to `Cas/Lang/` is a one-line lakefile change and a ruling, not a side
effect, and it is listed as owed at the end of this packet.

**The placement is verified, not reasoned.** PDD-8's builder found the
same trap by experiment mid-flight — a module planted under `Cas/Lang/`
with a `sorry` in it stayed GREEN, because nothing builds it — and the
coordinator circulated the warning. Two controls were run here rather
than trusting the argument above:

1. `Cas.Backend.SumAlgebra` appears by name in the build job list
   (`[72/95] Replayed Cas.Backend.SumAlgebra`), so it is a target and
   not a file the toolchain never opens.
2. A `sorry` planted in this module turns `lake --wfail build Cas
   CasBackend CasExamples CasWp` RED — exit 1, `declaration uses
   'sorry'`. Removing it returns exit 0, 95 jobs. So the gate that
   vouches for these theorems can fail, which is the only thing that
   makes its passing worth anything.

That second control is the estate's own discipline applied to itself:
`check:cas:obligations` runs `--self-test` before `--check` for exactly
this reason ("a gate that cannot fail proves nothing"). A green build
over an unbuilt module is the failure mode this packet's whole
escalation claim would otherwise rest on.

## The algebra

Carriers, all shipped, none introduced:

```
Sig            ⟨Op : Type, Ans : Op → Type⟩          Sig.lean:13-15
S ⊕ₛ T         ⟨S.Op ⊕ T.Op, Sum.elim S.Ans T.Ans⟩   Sig.lean:20-25
Prog S A       .pure a | .vis (e : S.Op) (k : S.Ans e → Prog S A)
                                                     Prog.lean:25-27
Prog.bind      the monad                             Prog.lean:31-33
Prog.op e      .vis e .pure                          Prog.lean:40
Prog.inl/.inr  Prog S A → Prog (S ⊕ₛ T) A            Prog.lean:43-50
Handler S M    ⟨handle : (op : S.Op) → M (S.Ans op)⟩ Handler.lean:42-43
interpret h    Prog S A → M A                        Handler.lean:47-49
Handler.sum    Handler S M → Handler T M
                 → Handler (S ⊕ₛ T) M                Handler.lean:63-66
idHandler      Handler S (Prog S)                    Representation.lean:63-64
failWith/require                                     Ops.lean:55-60
liftCas        Prog.inl at AgentSig                  Ops.lean:63
handleLlm      the hand-rolled AgentSig split        Interp.lean:184-187
```

Two handlers are DEFINED by this slice, and neither is a new type —
both are values of the shipped `Handler`:

```
inlHandler S T : Handler S (Prog (S ⊕ₛ T)) := ⟨fun op => .vis (.inl op) .pure⟩
inrHandler S T : Handler T (Prog (S ⊕ₛ T)) := ⟨fun op => .vis (.inr op) .pure⟩
llmOracleHandler o : Handler LlmSig (Prog CasSig) := ⟨fun (.infer q) => .pure (o q)⟩
```

`llmOracleHandler` is L30's right-hand side, spelled once so the law
can be stated as an equation between two functions rather than as
prose. `inlHandler`/`inrHandler` are the reviewer's own proposal
(handlers-semantics.md C.2 row 3.3: "`Prog.inl` / `Prog.inr` are
`interpret` of the injection handlers — makes 3.1/3.2 corollaries of
2.2 and kills the hand-rolled recursions"); this packet takes it, and
they are what makes ADQ-INL provable at all.

## The headings

```
REQUIRES   Nothing. Every law is total on its carrier: no partial
           operation, no side condition, no premise on any argument.
           In particular NO PREMISE ON `H`. The address function does
           not appear in a single statement in this slice — these are
           laws of the signature/program/handler algebra, strictly
           upstream of the store's admission judgment — so CAS-003's
           "premises on `H` are named at their lattice level" generates
           nothing here, and the packet says so rather than leaving a
           reader to wonder which lattice level was assumed.

           Run-relative note: no law below quantifies over starting
           words, because none of them mentions a word. L31 is the one
           statement a reader might expect to be run-relative — it is
           not: it is an equation between PROGRAMS (stratum 2), which
           is strictly stronger than the same claim at any word, and
           the claim-scope section says so.

ENSURES    There is no second state. Every declaration under contract
           is a pure function of its arguments, so `old` is vacuous and
           the two-state postcondition degenerates to the equations
           below.

DECREASES  Structural recursion on `Prog`, everywhere. Every induction
           and every definition in this slice recurses on `k r` — a
           constructor child of `.vis e k` — into the type's own
           structural order (CATALOG §4.3: "recurse on structurally
           included children and the decrease is free"). No fuel, no
           existential variant, no new well-founded order is owed:
           unlike PDD-2, nothing here runs anything.

           The private adversaries (`doubleInl`, below) recurse the
           same way and are total for the same reason. This matters:
           an adversary that failed to terminate would refute nothing.

FRAME      Reads: the shipped declarations named in "The algebra".
           Writes: nothing — no state, no store, no word, no address.

           The FILE frame is the load-bearing half. This slice adds
           TWO new files:
             library/cas/contracts/PDD-7.contract.md   (this packet)
             library/cas/Cas/Backend/SumAlgebra.lean   (the theorems)
           and edits NO existing file — not `Prog.lean`, not
           `Sig.lean`, not `Handler.lean`, not `Interp.lean`, not
           `Ops.lean`, not `lakefile.toml`, not `Cas/Lang/Lang.lean`.
           The consequence is checked, not assumed: the new module is
           outside `Walk.libraryImports`, so `surface`, `obligations`
           and `laws` cannot see it, and every byte gate in
           `check:cas` must stay identical.
```

## The laws, each with its falsifier

Every falsifier is EXECUTABLE against the Lean model — a counter-
`example`, a `¬ (∀ …)` theorem, or a `#guard`. Per CONTRACT.md the
falsifier must be executable against the artifact under contract; the
artifact here is the Lean model, and `check:cas` is the gate that
carries the slice to the host as a negative claim.

Battery, for every row below: `library/cas/Cas/Backend/SumAlgebra.lean`.

### The carrier's stragglers (§2.1)

```
LAW  L5    (Prog.op e).bind k = Prog.vis e k
           The smart constructor and the raw constructor agree. Every
           program written under R14a P2 ("programs are authored as
           smart constructors composed by bind") is a `.vis` tree only
           because of this equation, and it is stated nowhere.
FALS L5    exhibit S, e, k with (Prog.op e).bind k ≠ Prog.vis e k.
BATT L5    `Prog.op_bind`.

LAW  L7    (failWith r).bind f = failWith r
           Failure absorbs its continuation. Every user of `require`
           assumes it (THE-ALGEBRA §2.1 L7).
FALS L7    exhibit r, f with (failWith r).bind f ≠ failWith r.
BATT L7    `failWith_bind`.

LAW  L8    require true  r = Prog.pure ()
           require false r = failWith r
FALS L8    exhibit r with either equation failing.
BATT L8    `require_true`, `require_false`.
```

### The sum block (§2.3)

```
LAW  L21   (h.sum g).handle (Sum.inl op) = h.handle op
LAW  L22   (h.sum g).handle (Sum.inr op) = g.handle op
FALS L21/22 exhibit h, g, op where the composed handler answers with
           the wrong summand's meaning. The witness that makes this
           real is `swapSum` below: at S = T the arms can be exchanged
           and, with no law stated, nothing notices
           (handlers-semantics.md B.9's own witness).
BATT L21/22 `Handler.sum_handle_inl`, `Handler.sum_handle_inr`;
           adversary `swapSum` and `swapSum_not_sum`.

LAW  L23   interpret (h.sum g) p.inl = interpret h p
           — for EVERY target monad M and EVERY handler pair. The law
           every `liftCas` and `liftRootedCas` consumer assumes.
FALS L23   exhibit M, h, g, p with interpret (h.sum g) p.inl ≠
           interpret h p.
BATT L23   `interpret_inl`; the adversary `doubleInl` fires this
           falsifier against ITSELF (`doubleInl_not_interpret_inl`),
           which is what makes L23 the load-bearing row.

LAW  L24   interpret (h.sum g) q.inr = interpret g q
FALS L24   exhibit M, h, g, q with the two sides differing. The
           witness is `badAgentSum` below — the adversary that
           DISCARDS g (THE-ALGEBRA §3.2 ADVERSARY 1).
BATT L24   `interpret_inr`; `badAgentSum`, `badAgentSum_not_interpret_inr`.

LAW  L25   Prog.inl is a monad morphism:
             (Prog.pure a).inl = Prog.pure a
             (p.bind f).inl    = p.inl.bind (fun a => (f a).inl)
           and the same two for Prog.inr.
FALS L25   exhibit p, f with (p.bind f).inl ≠ p.inl.bind (·.inl ∘ f)
           — CATALOG §7.2's homomorphism square, at this square.
BATT L25   `Prog.inl_pure`, `Prog.inl_bind`, `Prog.inr_pure`,
           `Prog.inr_bind`.

LAW  L26   Prog.inl is injective; Prog.inr is injective.
           p.inl = q.inl → p = q.
FALS L26   exhibit p ≠ q with p.inl = q.inl.
BATT L26   `Prog.inl_injective`, `Prog.inr_injective`.

LAW  L30   Prog.handleLlm oracle
             = interpret (idHandler.sum (llmOracleHandler oracle))
           The right-hand side is a VALUE of the existing `Handler` —
           no new type. The hand-rolled AgentSig split at
           Interp.lean:184-187 IS an interpretation.
FALS L30   exhibit oracle, p where the hand-rolled recursion and the
           interpretation disagree.
BATT L30   `handleLlm_eq_interpret` (pointwise) and
           `handleLlm_eq_interpret_fun` (the function equation as
           THE-ALGEBRA states it).

LAW  L31   handleLlm oracle (liftCas p) = p
           The law every `runAgent` client assumes: lifting a store
           program into the agent language and handling inference away
           returns the program itself, on the nose.
FALS L31   exhibit oracle, p with handleLlm oracle (liftCas p) ≠ p.
BATT L31   `handleLlm_liftCas`; and `handleLlm_liftCas_via_laws`, the
           same fact re-derived from L30 + L23 + `interpret_id`, so
           the packet's own laws are shown to compose rather than
           merely coexist.
NOTE L31   **L31 IS WRONG-BUT-PASSING ON ITS OWN.** Amendment, breaker
           hand (HOLE-2). The docstring called this "the law every
           `runAgent` client assumes", which reads as a standalone
           client guarantee. It is not one. `liftCas p` contains no
           `infer` node, so L31 constrains `handleLlm` ONLY on
           `Prog.inl`'s image and says nothing whatever about the
           oracle. The witness is `badHandleLlm` — an implementation
           that DISCARDS the oracle and answers every inference with
           the empty string — which satisfies L31 at every universe,
           by the same induction the real one uses. A client leaning
           on L31 alone has no oracle guarantee at all.

           **L30 is the law that carries the exclusion**, and it is in
           this packet, so the law SET is adequate — what was missing
           was the boundary. A `runAgent` client wanting an oracle
           guarantee must cite L30, not L31. The adversary is adopted
           into the module's `Adversary` namespace beside the other
           three so the boundary cannot be relaxed without a red
           build.
```

### The machinery, stated because it is load-bearing

```
LAW  INJ-H interpret (inlHandler S T) p = p.inl
           interpret (inrHandler S T) q = q.inr
           The hand-rolled injections ARE interpretations
           (handlers-semantics.md C.2 row 3.3).
FALS INJ-H exhibit p where the interpretation and the recursion differ.
BATT INJ-H `interpret_inlHandler`, `interpret_inrHandler`.

LAW  SUM-ID (inlHandler S T).sum (inrHandler S T) = idHandler
           The injection handlers sum to the identity handler. This is
           the bridge ADQ-INL crosses.
FALS SUM-ID exhibit an operation on which the two disagree.
BATT SUM-ID `sum_inlHandler_inrHandler`.
```

Extensionality for handlers (`h.handle = g.handle → h = g`) is
THE-ALGEBRA's **L16 and it belongs to PDD-8**, which is running in
parallel and owns that row. This packet needs it as machinery and does
not claim it: the module carries a `private` helper under a different
name (`handler_eq_of_handle`) with a docstring saying so, and no public
declaration here is named `Handler.ext`. On merge, PDD-8's public L16
and this private helper coexist without collision, and the row stays
PDD-8's.

### The adequacy laws — what excludes the wrong implementations

This is the section the ticket asks for ("state what excludes it"), and
it is stated as THEOREMS rather than as reasoning.

```
LAW  ADQ-SUM  L21 and L22 are CATEGORICAL for Handler.sum:
                for every k : Handler (S ⊕ₛ T) M,
                  (∀ op, k.handle (.inl op) = h.handle op) →
                  (∀ op, k.handle (.inr op) = g.handle op) →
                    k = h.sum g
              So `badSum` and `swapSum` are not merely refuted by an
              example — no wrong-but-passing `Handler.sum` EXISTS.
FALS ADQ-SUM  exhibit k satisfying both hypotheses with k ≠ h.sum g.
BATT ADQ-SUM  `Handler.sum_unique`.

LAW  ADQ-INL  L23 is CATEGORICAL for Prog.inl:
                for every ι : {A : Type} → Prog S A → Prog (S ⊕ₛ T) A,
                  (∀ M [Monad M] [LawfulMonad M] (h : Handler S M)
                     (g : Handler T M) {A} (p : Prog S A),
                       interpret (h.sum g) (ι p) = interpret h p) →
                  ∀ {A} (p : Prog S A), ι p = p.inl
              and the mirror statement for `inr`. The proof is the
              instantiation M := Prog (S ⊕ₛ T), h := inlHandler,
              g := inrHandler, closed by SUM-ID, `interpret_id` and
              INJ-H.
FALS ADQ-INL  exhibit ι satisfying the hypothesis at every lawful
              target and every handler pair, with ι p ≠ p.inl at some
              p. `doubleInl` is the candidate the ticket names, and the
              theorem says the exhibit does not exist.
BATT ADQ-INL  `inl_unique_one_target` with `syntactic_hyp_iff`, and
              `inr_unique_one_target` with `syntactic_hyp_iff_inr` —
              the same conclusion from the single instance each proof
              actually consumes. `Prog.inl_unique` and
              `Prog.inr_unique` are their corollaries. All four adopted
              from the attack record.

LAW  ADQ-L30  L30's right summand is FORCED. Adopted from the attack
              record; **the packet omitted this row and should not
              have.** L30 says `handleLlm oracle` IS an interpretation
              of `idHandler.sum (llmOracleHandler oracle)`; it does not
              by itself say that `llmOracleHandler oracle` is the ONLY
              right summand for which that holds. It is:
                for every g : Handler LlmSig (Prog CasSig),
                  (∀ A p, p.handleLlm oracle = interpret (idHandler.sum g) p)
                    → g = llmOracleHandler oracle
              So the ADQ block is now complete across all three
              definitions the slice touches: `Handler.sum`,
              `Prog.inl`/`inr`, and L30's oracle summand.
FALS ADQ-L30  exhibit g ≠ llmOracleHandler oracle that also presents
              `handleLlm` as an interpretation.
BATT ADQ-L30  `llmOracleHandler_unique_one_program` with
              `l30_hyp_iff` — the summand is forced by the hypothesis
              at single-operation programs alone;
              `llmOracleHandler_unique` is its corollary.

NOTE ADQ     **The shape lesson is applied uniformly.** HOLE-1 was
             never a fact about `Prog.inl`: it was a fact about a PROOF
             SHAPE — a categoricity whose hypothesis is ∀-quantified
             while its proof consumes one instance, at which the
             hypothesis is equivalent to the conclusion, states less
             than it proves. The first fix pass corrected the row the
             breaker pointed at and left the same shape in two others
             (`AttackAmended.lean` §C, NOTE-7). All three ADQ rows now
             carry the narrowed statement as PRIMARY and the
             ∀-quantified one as its COROLLARY:

               ADQ-INL   `inl_unique_one_target`   ← `Prog.inl_unique`
               ADQ-INR   `inr_unique_one_target`   ← `Prog.inr_unique`
               ADQ-L30   `llmOracleHandler_unique_one_program`
                                         ← `llmOracleHandler_unique`

             **ADQ-SUM is exempt, and provably so.** `Handler.sum_unique`
             does not have the shape: its premises are already
             pointwise-minimal, and the breaker's `sum_unique_iff`
             upgrades it to an equivalence while
             `sum_unique_needs_left_premise` /
             `sum_unique_needs_right_premise` show neither premise is
             spare. It is left as it stands, and this note says why
             rather than leaving the asymmetry to be read as an
             oversight.
NOTE ADQ-INL  The hypothesis is STRONG — it quantifies over every
              lawful target monad — so the obvious attack is that the
              theorem is vacuous: a uniqueness result whose premise
              nothing satisfies proves nothing at all. It is not
              vacuous, and the witness is in the same file: L23
              (`interpret_inl`) IS the statement that `Prog.inl`
              satisfies the premise, proved for every `M` with a bare
              `Monad` instance — weaker than the `LawfulMonad` the
              premise asks for. So the premise has exactly one
              inhabitant and `interpret_inl` exhibits it.

              AMENDED, breaker hand (HOLE-1). This note previously
              said the wide quantifier was "not an accident of
              convenience" and was the mechanism of the categoricity.
              **That was false, and it is corrected here rather than
              softened.** What is true:

              - **The law is SYNTACTICALLY categorical.**
                `Prog.inl_unique`'s proof consumes exactly ONE instance
                of its hypothesis — `M := Prog (S ⊕ₛ T)`,
                `h := inlHandler`, `g := inrHandler` — and at that
                instance the hypothesis is EQUIVALENT to the
                conclusion, by the same two rewrites the proof
                performs (`syntactic_hyp_iff`). The narrowed law
                `inl_unique_one_target` is therefore strictly stronger
                than the shipped one, and it is adopted below;
                `Prog.inl_unique` is now its corollary.
              - **The counting target never enters.** `StateT Nat Id`
                is the device of the REFUTATION
                (`doubleInl_not_interpret_inl`), not of the
                categoricity. The categoricity is carried entirely by
                the INITIAL monad.
              - **The quantifier is generality, not mechanism.** But it
                is not free either, and the honest constraint is
                provable: the target must RECORD effects. `Id` does
                not — `doubleInl` satisfies the Id-restricted
                hypothesis at every handler pair, so
                `narrowing_to_Id_fails` shows ADQ-INL becomes FALSE
                under that narrowing. `Prog (S ⊕ₛ T)` does. That is
                the sharper and checkable version of what this note
                was reaching for.
              - **The `RefM` comparison is UNPROVED, on both sides,
                and is not implied here.** The old text said weakening
                to `RefM` "would make the law exactly as blind as the
                word gate". Nothing in this packet or in the attack
                record proves that: it needs
                `ObsEq H (liftCas p) (doubleInl p)`, which the
                claim-scope section below explicitly declines to prove
                and which the breaker also failed to close (attack
                record §8, failed attempt 6). It is OPEN, not
                established, and this note no longer gestures at it.

LAW  ADQ-DBL  THE-ALGEBRA §3.2, verbatim, on the doubling injection:
                "KILLED BY interpret_inl (L23) together with `inl` is a
                 monad morphism (L25); nothing weaker separates them"
              (prog-carrier.md H-3 states it identically as "S3
              together with S5; nothing weaker separates them").
              Two conjuncts, both under attack:
                (a) L23 refutes `doubleInl`;
                (b) L25 is NECESSARY — L23 alone does not separate them.
FALS ADQ-DBL  (a) is falsified by exhibiting M, h, g, p at which
              `doubleInl` satisfies L23. (b) is falsified by EITHER
              exhibiting a proof that `doubleInl` satisfies L25 — in
              which case L25 excludes nothing and cannot be doing the
              work the record credits it with — OR by proving L23
              categorical (ADQ-INL), in which case nothing weaker is
              needed because L23 alone already suffices.
BATT ADQ-DBL  `doubleInl`, `doubleInl_not_interpret_inl`,
              `doubleInl_pure`, `doubleInl_bind`, and ADQ-INL.
```

ADQ-DBL is written as a law of the RECORD, not of the code, and it is
written before the proof runs. If its second conjunct survives, the
review document is confirmed. If it falls, the falsification is data
and lands in the Breaks ledger below with its witness — that is the
whole point of stating it here rather than quietly proving the version
that turns out to be true.

## The adversaries, kept in the tree

Three, each a `private` definition in the battery module with its
refutation beside it. They are record, not scratch (BREAKER.md, "attack
artifacts are record"), and they stay so a later hand cannot relax a
law back without a red build.

```
swapSum     : at S = T, the sum with its arms exchanged.
              Satisfies every law that existed before this packet
              (there were none). Refuted by L21.

badAgentSum : Handler AgentSig M built from a CasSig handler alone,
              answering every `infer` with `pure ""` and DISCARDING g.
              THE-ALGEBRA §3.2 ADVERSARY 1. Satisfies the L21 and L23
              analogues — proved, so the reader can see which law does
              the work — and is refuted by L22/L24 and by ADQ-SUM.

doubleInl   : performs every operation TWICE, keeps the first answer.
              THE-ALGEBRA §3.2 ADVERSARY 2, the ticket's named
              canonical wrong-but-passing candidate. The word gate is
              blind to it BY CONSTRUCTION (a second put of the same
              node is `duplicate` and leaves the word unchanged,
              Handler.lean:85; a second load is `Word.find` again;
              `fail` answers `Empty`), so the statement is the whole
              of the protection. Refuted by L23, at a handler that
              COUNTS operations — which is exactly the observation the
              word cannot make.
```

The counting handler is the methodological point of this packet and is
called out so it is not read as a toy: L23's quantification over EVERY
target monad is not generality for its own sake. It is what puts an
operation-counting observation inside the law's reach, and the
operation count is precisely the thing THE-ALGEBRA §3.2 says the
estate's only mechanical check cannot see. A law stated only at
`RefM` would be blind in the same way the gate is.

## Claim-scope — what these theorems do NOT say

The anti-overclaim class, written before the proofs so it cannot be
written to fit them.

- **Not claimed: anything about host code.** No TypeScript is a proof
  subject here; no generated byte moves and no word-equality vector is
  added. No soundness word attaches to any host artifact (estate C5).
- **Not claimed: `ObsEq H (liftCas p) (doubleInl p)`.** THE-ALGEBRA
  §3.2 and prog-carrier H-3 assert that the doubling injection is
  word-invisible for every store program, and this packet REPEATS that
  assertion as motivation without proving it. It is a claim about
  `referenceHandler` at `RefM`, not about the sum algebra, and proving
  it needs `put`-idempotence and `load`-purity lemmas this slice does
  not have. What is proved is the positive direction that matters:
  `doubleInl` is refuted at a handler that observes the count. A reader
  must not take this packet as evidence that the word gate IS blind —
  only that the laws do not depend on its not being.
- **Not claimed: L27 or L28.** `⊕ₛ` has no unit (`Sig.empty` does not
  exist) and is not associative or commutative as an equation in Lean.
  THE-ALGEBRA marks both "not stateable" pending ruling Q7 and this
  packet does not reopen them. So `⊕ₛ` is NOT proved to be a monoidal
  structure, and nothing here should be read as saying signatures form
  a symmetric monoidal category.
- **Not claimed: L29.** That our `⊕ₛ` + `inl`/`inr` is ITrees' `E +' F`
  with `Subevent` stays ASSERTED ✗. `Subevent` is a resolution class
  closed under nesting; ours is two hand-applied functions. Proving
  L25/L26 does not close that gap, and this packet does not pretend it
  does.
- **~~Not claimed: L32.~~ CLAIMED — the row is DISCHARGED.** Amended,
  breaker hand. The original text said L30 "makes it a corollary … but
  the corollary is not stated, so the row stays OWED". That understated
  what the slice already had: the corollary is two lines, and it is now
  stated as `handleLlm_bind` (adopted from the attack record).
  `handleLlm_bind` follows from L30 plus core `interpret_bind` at the
  shipped `LawfulMonad (Prog S)`, with no induction of its own.

  **This also settles a PDD-8 boundary, and the direction matters.**
  PDD-8's ticket names the estate's asserted-not-proved "`handleLlm`
  interprets by monad morphism" (`Interp.lean:19,181-183`) as part of
  its territory. The breaker's grep confirms there is no declaration
  behind that prose anywhere in `library/cas` or `.staging` — it is a
  docstring claim and nothing more. **PDD-7 therefore DISCHARGES that
  boundary rather than depending on it**: no theorem in this slice
  rests on the assertion, and `handleLlm_bind` now supplies what the
  docstring was claiming. Cross-cite: PDD-8's packet should record L32
  as carried here and not re-prove it.
- **Not claimed: the categoricity at every universe.** NOTE-5 of the
  attack record, adopted. `interpret` forces `A : Type`, so
  `Prog.inl_unique`, `inl_unique_one_target`, `Prog.inr_unique`,
  `handleLlm_eq_interpret` and `llmOracleHandler_unique` all pin their
  subjects at **`Type 0` only**, while the shipped `liftCas` and
  `Prog.handleLlm` are universe-polymorphic (`{A : Type u_1}`), and
  L25/L26/L31 are proved at `Type u`. The packet disclosed this for L30
  and not for the ADQ block; it is disclosed for both now.
  Unexploitable in practice — no Lean definition can branch on universe
  level — but as stated the categoricity does not reach the universes
  its subject is typed at, and that is a real gap between the theorem
  and the sentence a reader would write from it.
- **Not claimed: that any effect-recording target will do.** The
  quantifier's honest constraint has one proved lower bound and no
  proved characterization. `Id` is provably NOT enough
  (`narrowing_to_Id_fails`: `doubleInl` satisfies the Id-restricted
  hypothesis at every handler pair, so ADQ-INL is FALSE narrowed to
  `Id`); the initial monad `Prog (S ⊕ₛ T)` provably IS
  (`inl_unique_one_target`). Which targets in between suffice is not
  characterized here.
- **Not claimed: that the counting recipe transfers to `CasSig`.**
  NOTE-2 of the attack record, adopted, and it corrects a real defect
  in the module's own prose. `Handler CasSig (StateT Nat Id)` is
  **uninhabited** — `CasE.fail` answers `Empty` and `Id` has no branch
  to put it in — so the module docstring's recipe ("a target monad
  where an operation is visible: `StateT Nat Id`") is available only at
  the toy `TickSig`. The refutation is sound, because it refutes a
  ∀-statement and a witness anywhere suffices; but a reader carrying
  the recipe to the store language finds it does not typecheck. The
  substitution that works is `StateT Nat (Except Unit)`.
- **Not claimed: anything about nondeterministic or stateful oracles.**
  L30/L31 quantify over `oracle : String → String` — total,
  deterministic, pure — and every such function is covered. Two
  identical prompts in one program therefore always get the same
  answer, by theorem. A history-dependent oracle is not an oracle this
  quantifier ranges over: it would be a `Handler LlmSig M` for
  state-carrying `M`, and `interpret (idHandler.sum g)` then lands in
  `M` rather than in `Prog CasSig`, which `handleLlm`'s codomain
  forbids. `Interp.lean:21-22`'s "the oracle's nondeterminism enters
  only as the recorded answer" is a modelling stipulation the TYPE
  enforces, not a theorem about oracles. (Breaker's §6, recorded
  because this packet's claim-scope did not state it.)
- **Not claimed: the consolidation.** handlers-semantics C.2 row 3.4
  offers "or delete `handleLlm` and define it this way". L30 proves
  the two agree; DELETING the hand-rolled recursion would edit
  `Interp.lean` and move the surface ledger, which the fence forbids
  and which is a ruling in any case. `Roots.stepRooted` and any
  incoming `WordSig` split remain hand-rolled and unproved — this
  packet gives them the law they can be claimed against, and claims
  nothing about them.
- **Not claimed: universe generality for L30.** `interpret` lands in
  `M : Type → Type v`, so its `A` is `Type`. L30 is therefore stated at
  `A : Type`. L25, L26 and L31 are proved by direct induction and hold
  at `A : Type u`; the packet states each at the widest universe its
  proof actually reaches, and does not silently narrow the others to
  match.
- **Not claimed: that this module is in the library's ledgers.**
  `Cas.Backend.SumAlgebra` is built by the `CasBackend` glob and
  kernel-checked by `lake build`, and it is outside
  `Walk.libraryImports`, so it is invisible to the surface, obligation
  and law ledgers — which is exactly why the "moves no bytes" gate
  holds. Promoting it into that walk is a promotion, and a promotion
  is a ruling. (Same device and same disclosure as PDD-2's `CasWp`.)
- **Not claimed: that the exhibits file was used.** The ticket cites
  `.staging/algebraic-review/handlers-semantics-exhibits.lean` §1, §2,
  §6 as carrying proof sketches. That file was NOT TRACKED at this
  branch's base (`00ea1519`) — it was gitignored, so it did not exist
  in this worktree — and every proof in this slice was therefore
  developed from the carriers and checked by the kernel, with the
  review documents' law ROWS cited as prior art for the STATEMENTS
  (THE-ALGEBRA §2.1/§2.3, handlers-semantics C.2 §3, prog-carrier
  S1–S10). Main tracked the file at `b9283eda`, merged in at
  `7a3d558d`; it is verified here and the five overlapping statements
  agree with it, item by item, in the Breaks section. So the credit is
  shared where it overlaps and nothing was taken on trust.

## Obligation classes in play

`adequacy` — the class this packet is built around, and the only one
with real work in it: ADQ-SUM and ADQ-INL discharge it by proving the
law sets categorical, and ADQ-DBL puts the record's own account of it
under attack. `abstraction` — §9.5's square, at `Prog.inl` as the
abstraction function (L23, L25) and §9.4's exported observation (L26).
`algebraic-laws` — unit, morphism, injectivity. `claim-scope` — the
section above, and the L27/L28/L29/L32 boundary in particular.
`conformance` — the negative byte gate. `termination` — structural, on
the constructor children, including for the adversaries.

`domain`, `contract`, `frame`, `invariant`, `loops` and
`mutation-frames` generate nothing: there is no partial operation, no
state, no two-state postcondition, no representation invariant and no
iteration anywhere in this slice. Per CONTRACT.md, classes that do not
apply generate no boilerplate, and the packet says which and why
rather than leaving the omission to be read as an oversight.

## Gates

```
lake --wfail build Cas CasBackend CasExamples CasWp   (from library/cas)
mise run check:cas                                    (byte-identical)
mise run check:cas:surface                            (byte-identical)
mise run check:cas:obligations                        (byte-identical)
mise run check:cas:laws                               (byte-identical)
git status                                            (clean)
```

No `sorry`, no `native_decide`, no new axiom: an axiom census over
every headline declaration in the module is printed BY the run
(`#print axioms`, module tail), so the claim is read off the build
rather than asserted here.

**Results at `03ca1435`.** All green. `lake --wfail build` completed
(95 jobs); `mise run check:cas` exited 0 with every byte gate `ok`;
the three supportInterpreter ledgers are byte-identical and unmoved —
`surface/cas-surface.json` 955041 bytes, 2026 declarations;
`surface/cas-obligations.json` 17363 bytes, 68 obligations;
`surface/cas-laws.json` 9825 bytes, 9 of 37 rulings bound. The
declaration count is the mechanical confirmation that the new module is
outside `Walk.libraryImports`: the module carries 52 public
declarations and one private helper, and the surface ledger did not
move by one byte. `git status` clean.

The census itself: `propext` and `Quot.sound` only, across every
headline theorem — `Prog.op_bind` depends on no axiom at all. No
`sorryAx`, no `Classical.choice`.

## Owed, not done here

- **The module's home.** `Cas.Backend.SumAlgebra` should be
  `Cas.Lang.Sum`. That is a `lakefile.toml` edit (or an import in
  `Cas/Lang/Lang.lean`, which moves the surface ledger and is a
  promotion). Named here so it is a decision someone takes, not a
  thing that quietly stays wrong.
- **The hand-rolled sum consumers.** `Roots.stepRooted`
  (`Roots.lean:69-81`) and the incoming `WordSig`/`stepWorded` split
  still bypass `Handler.sum`. They now have laws to be claimed
  against; claiming them edits fenced files.
- **`ObsEq H (liftCas p) (doubleInl p)`** — the word-blindness claim
  itself, still unproved in either direction.

## Breaks

The ledger of successful falsifications, per CONTRACT.md §The break
ledger. It was empty when this packet was committed at `8e7fe66a`,
before any theorem existed. One row has landed since.

```
BROKE      the RECORD, not an implementation. The falsifier fired
           against a claim in `.staging/algebraic-review/`, and no
           shipped declaration is wrong — every law in this packet is
           true and every one of them stays.
LAW        THE-ALGEBRA.md §3.2, verbatim:
             "KILLED BY  interpret_inl (L23) together with `inl` is a
              monad morphism (L25); nothing weaker separates them"
           and prog-carrier.md H-3, identically:
             "KILLED BY  S3 (interpret_inl) together with S5 (inl is a
              monad morphism); nothing weaker separates them."
           Read as stated, the claim has two parts: L23 does not
           suffice alone, and L25 supplies what is missing.
WITNESS    `doubleInl` — THE-ALGEBRA §3.2's own ADVERSARY 2, the
           injection that performs every operation twice and keeps the
           first answer — SATISFIES L25 in full, and L26 besides:

             Adversary.doubleInl_pure       (Prog.pure a) ↦ Prog.pure a
             Adversary.doubleInl_bind       (p.bind f) ↦ p.bind (·∘f)
             Adversary.doubleInl_injective  injective

           all kernel-checked in
           `library/cas/Cas/Backend/SumAlgebra.lean` at `03ca1435`,
           by the same induction the real injection uses. So L25
           excludes the adversary from nothing and cannot be half of
           what separates it.

           The second half of the same finding, from the other
           direction: `Prog.inl_unique` proves L23 CATEGORICAL —
           satisfying it at every lawful target monad and every handler
           pair forces `Prog.inl` pointwise, `doubleInl` included. So
           "nothing weaker separates them" is false twice over: L23
           alone already separates them, and the thing offered as the
           needed supplement separates nothing.

           The refutation of the adversary is `interpret_inl` and it
           alone: `Adversary.doubleInl_not_interpret_inl`, witnessed at
           `TickSig` and a handler into `StateT Nat Id`, where the
           doubled program spends 2 operations against the real one's
           1.
CLASS      claim-scope. The stated boundary of the record's claim did
           not equal its actual coverage — the attribution of which law
           does the work was wrong, in the direction of crediting a law
           that does none. It is the same shape as PDD-1's second
           breaker row (right theorem, wrong subject), and it matters
           for the same reason: a later hand reading §3.2 would think
           L25 was load-bearing for adequacy and might weaken L23 while
           keeping it.
FIXED-BY   03ca1435. The corrected attribution is carried in the
           module's own prose (the section "What L25 contributes to
           killing it — nothing") and by the three theorems that
           witness it, so the claim cannot be quietly restored without
           a red build. NOT fixed by amending `.staging/`: those are
           review documents of a dated pass, this packet is the
           estate's answer to them, and rewriting the reviewer's text
           would destroy the record the ledger exists to keep.
```

What the break is worth beyond this ticket. The general lesson is about
where a separating law must be QUANTIFIED, not about sums. L25 is an
equation between two programs, so it can only see structure that
survives being written down; the doubling injection's defect is not
structural — it is a defect in what the program DOES, and the doubling
is structurally as lawful as the original. Only a law quantified over
target monads reaches an observation (here: the operation count) that
separates them. Any future law meant to exclude a
performs-too-much/too-little implementation — for `Roots.stepRooted`,
for the incoming `WordSig` split, for a transport handler — inherits
the same requirement, and the estate now has one proved instance of
it to copy rather than a plausible-sounding pair to copy.

Two smaller findings, recorded rather than filed:

- **The cited exhibits files do not exist.**
  THE-ALGEBRA's Sources block (`:42-44`) names
  `handlers-semantics-exhibits.lean` and `word-store-exhibits.lean` as
  "the kernel-checked exhibit files" it is written against. Neither has
  ever been committed on any branch in this history: the only commit
  that ever added files to `.staging/algebraic-review/` is `5e93b29f`,
  and it added seven `.md` files and no `.lean`. The consequence is
  not cosmetic — **nine OWED rows of the law ledger cite them as the
  carrier of their proof**: L5, L16, L17, L18, L23, L24, L31, L34, L35
  ("proved in `handlers-semantics-exhibits.lean` §2", "exhibits §4,
  nine lines"), plus L79's witness in `word-store-exhibits.lean` and
  four prose citations down to a line number
  (`handlers-semantics-exhibits.lean:137`, `:155`, `:171`). PDD-7's
  and PDD-8's tickets both send their agents to read the file. So
  "proved in exhibits §N" currently reads as a discharge and is a
  citation to nothing.

  **CORRECTION, same hand, after main moved.** The observation above is
  true of git; the diagnosis drawn from it is wrong, and the bullet is
  left standing rather than swapped out so the error is legible. The
  files existed on the operator's disk the whole time and were
  **gitignored** — invisible to a worktree, which is why this castle
  could not open them. Main tracked them at `b9283eda` ("the review's
  exhibit files — THE-ALGEBRA's evidence base was gitignored"), merged
  into this branch at `7a3d558d`. The right claim was the weaker one:
  not "these do not exist" but "these are unreachable from any clone",
  which they were until `b9283eda`. A worktree-isolated agent sees
  exactly the tracked tree, so the two are indistinguishable from
  inside one — and this packet asserted the stronger.

  **The exhibits are verified, and this slice agrees with them.**
  `lake env lean ../../.staging/algebraic-review/handlers-semantics-exhibits.lean`
  from `library/cas` exits 0 against this branch. Correspondence,
  statement by statement:

  | exhibit | this slice | relation |
  |---|---|---|
  | §1 `interpret_sum_inl` | `interpret_inl` (L23) | same statement, same proof idea (`bind_congr`) |
  | §1 `interpret_sum_inr` | `interpret_inr` (L24) | same |
  | §2 `op_bind` | `Prog.op_bind` (L5) | same statement, `rfl` both |
  | §6 `handleLlm_liftCas` | `handleLlm_liftCas` (L31) | same statement, same induction |
  | §3 `handler_ext` | `handler_eq_of_handle` (private) | same proof term; the ROW is PDD-8's L16 and stays PDD-8's |

  All five were developed here from the carriers before the file was
  reachable, and they agree. That is a better outcome than having
  copied them, and it is why the packet reports the agreement rather
  than quietly adopting the citation.

  What the exhibits do NOT carry, and this slice adds: L7, L8, L21,
  L22, L25, L26, L30, INJ-H, and all three categoricity theorems
  (`Handler.sum_unique`, `inl_unique_one_target`/`Prog.inr_unique`,
  `llmOracleHandler_unique`), plus the four adversaries and their
  refutations. The exhibits show the named
  laws are provable — the report's own claim that "the gap is a
  statement gap and not a proof gap". They do not ask whether the law
  SET is strong enough to exclude a wrong implementation, which is the
  question this packet is built around and the reason it is not
  redundant with them.

  One claim-scope line above needs adjusting in light of them: L32
  (`handleLlm` respects `bind`) IS carried, by exhibit §6
  `handleLlm_bind`. (Superseded: the row is now DISCHARGED in this
  slice, by the breaker's two-line derivation from L30 — see the
  claim-scope entry.)
- **`Handler.sum` still has no call site**, and this packet does not
  give it one. It now has laws and a categoricity theorem, so the
  hand-rolled consumers can be claimed against it; making that claim
  edits fenced files and is the next ticket's work, not this one's.

## The attack — the independent breaker's pass

Record: `library/cas/contracts/attacks/PDD-7/` on branch
`attack/opus-cc-mac/pdd-7`. **Two passes, both STANDS, no BREAK in
either.** Pass 1 (`Attack.lean`, `RESULTS.md` @ `b509cb20`, against
castle `d714ef14`): 2 HOLE, 6 NOTE. Pass 2 (`AttackAmended.lean` @
`cf91531c`, against the fix pass `e1ceb205`): **STANDS-AMENDED** —
both holes confirmed closed structurally, the declined adoption of
`inl_unique_via_initiality` concurred with, and one new NOTE-7 whose
row is the third in the ledger below. No theorem in this module was
false in either pass; every finding was prose or structure against
kernel-checked fact. No theorem in the module is false, every gate reproduced to the
byte, the axiom census reproduced over a strictly larger declaration
set (55 constants, not the 16 the module prints), the commit order was
confirmed packet-first, and the sorry-control was repeated by the
breaker's own hand with both signals firing.

Two results run in the packet's favour and are recorded here rather
than left in the attack tree:

```
RESULT     the break ledger's row is CONFIRMED IN BOTH DIRECTIONS, by
           a route this castle does not use. `doubleInl_factors` proves
           the adversary is `Prog.inl ∘ dup` — the real injection
           precomposed with a monad-morphism ENDOMORPHISM of `Prog S` —
           from which L25 and L26 for the adversary fall out of the
           same laws for `Prog.inl` and for `dup`, with no induction
           over the adversary at all. Half (b) of §3.2's claim is
           false, and now for a stated structural reason rather than
           by exhibition.
CLASS      adequacy — and the generalization is the part worth keeping:
           EVERY equation-between-programs law is blind to the whole
           family `Prog.inl ∘ φ` for `φ` a monad-morphism endomorphism,
           not merely to this one member. The packet's closing
           paragraph said this as a lesson; the breaker made it a
           theorem.

RESULT     no adversary escaped. The breaker built three of its own —
           `swapTwoInl` (reorders two operations), `dropInl` (elides an
           operation whose answer is provably unused), `putDoubleInl`
           (doubles only the `put` tag, at `CasSig` itself) — and all
           three die. A1 and A2 die twice over, to L25 and L26
           respectively, which is the sharpening this packet needed:
           **"L25 excludes nothing" would be wrong; "L25 excludes THE
           ADVERSARY from nothing" is what is true**, and the module's
           heading is accurate only as scoped. L25 and L26 earn their
           place against other injections; `doubleInl_factors` is the
           exact account of the family they cannot see.
CLASS      adequacy — discharged. An escaping injection is provably
           impossible for the stated type: ADQ-INL is categorical, so
           every ι either fails L23 at some lawful target or IS
           `Prog.inl`.
```

Adopted into the module, credited by path and commit per the PDD-2
precedent — the breaker proved these first and the packet says so. All
six are `library/cas/contracts/attacks/PDD-7/Attack.lean` @ `b509cb20`:

| adopted | what it does | record |
|---|---|---|
| `syntactic_hyp_iff` | the hypothesis at the consumed instance IS the conclusion | §2 |
| `inl_unique_one_target` | ADQ-INL from ONE target; `Prog.inl_unique` becomes its corollary | §2 |
| `doubleInl_interpret_inl_Id` + `narrowing_to_Id_fails` | `Id` is provably not a separating target | §2 |
| `dup`, `dup_bind`, `dup_injective`, `doubleInl_factors` | the structural account of the break | §3 |
| `llmOracleHandler_unique` | ADQ-L30 — the oracle summand is forced | §5 |
| `handleLlm_bind` | L32, discharged from L30 in two lines | §5 |
| `badHandleLlm` + three refutations | HOLE-2's witness, into the `Adversary` namespace | §5 |

And from the RE-ATTACK, `AttackAmended.lean` @ `cf91531c` (NOTE-7 —
the shape lesson reached two rows the first fix pass did not):

| adopted | what it does | record |
|---|---|---|
| `syntactic_hyp_iff_inr` | the `inr` mirror of the equivalence | §C1 |
| `inr_unique_one_target` | ADQ-INR narrowed; `Prog.inr_unique` becomes its corollary | §C1 |
| `l30_hyp_iff` | ADQ-L30's hypothesis at one operation IS its conclusion | §C2 |
| `llmOracleHandler_unique_one_program` | ADQ-L30 narrowed to single-operation programs | §C2 |

Six NOTEs were raised. NOTE-1, NOTE-2 and NOTE-5 are adopted into
claim-scope above. NOTE-3 is adopted into the module's L25 heading and
into the second RESULT block. NOTE-4's instrument correction is fixed
in the module tail. NOTE-6 offered four results; all four are adopted.

## Breaks — the breaker's rows

Two rows, entered by the breaker's findings after the independent
attack on `d714ef14`. Both are `claim-scope`, both are prose against
kernel-checked fact, and **neither required a theorem to change** — the
castle held and the map was wrong, which is the same shape as PDD-1's
two breaker rows.

```
BROKE      d714ef14 — theorem true, ACCOUNT of it false.
LAW        this packet's NOTE ADQ-INL (at `24b6fe30`) and the module
           docstring, verbatim:
             "The strength is also not an accident of convenience. …
              Only an observation can, and a handler into an arbitrary
              monad is where observations live. Weakening the
              quantifier to `RefM` would make the law exactly as blind
              as the word gate."
           i.e. the claim that ADQ-INL's quantification over every
           target monad is the MECHANISM of the categoricity.
WITNESS    `inl_unique_one_target` — the same conclusion from a
           hypothesis at ONE monad and ONE handler pair, strictly
           stronger than the shipped law — together with
           `syntactic_hyp_iff`, which shows that instance of the
           hypothesis is EQUIVALENT to the conclusion by exactly the
           two rewrites `Prog.inl_unique`'s proof performs. The
           counting target `StateT Nat Id` never enters the proof; the
           theorem is carried entirely by the initial monad.
           `inl_unique_via_initiality` closes the second door,
           reaching the same conclusion through
           `eq_of_forall_interpret` + ADQ-SUM and bottoming out at the
           same instance.
           Second half: the `RefM` sentence rests on
           `ObsEq H (liftCas p) (doubleInl p)`, which THIS PACKET'S own
           claim-scope declines to prove and which the breaker also
           failed to close (record §8, attempt 6). The packet asserted
           as motivation a thing it refused to assert as a claim.
CLASS      claim-scope — the stated boundary did not equal the actual
           coverage, and the error was OPERATIVE: it instructed a later
           hand that the wide quantifier must not be weakened, when the
           real constraint is different and provable (`Id` fails, the
           initial monad suffices).
FIXED-BY   this commit. NOTE ADQ-INL is rewritten to state what is
           true, `inl_unique_one_target` and `narrowing_to_Id_fails`
           are adopted so the correction is carried by theorems and not
           only by prose, and the `RefM` gesture is withdrawn and
           marked OPEN on both sides.
```

```
BROKE      d714ef14 — law true, REACH overstated.
LAW        L31 as this packet stated it, and the module docstring:
             "handleLlm oracle (liftCas p) = p
              The law every `runAgent` client assumes."
           presented as a standalone client guarantee.
WITNESS    `badHandleLlm` — an implementation that DISCARDS THE ORACLE
           ENTIRELY and answers every inference with the empty string.
           It satisfies L31 in full, at every universe, by the same
           induction the real one uses, because `liftCas p` contains no
           `infer` node. `badHandleLlm_differs` and
           `badHandleLlm_not_interpret` exhibit the disagreement at
           `infer "x"` under `wildOracle`. So a `runAgent` client
           leaning on L31 alone has NO oracle guarantee.
CLASS      claim-scope — L31's reach stops at `Prog.inl`'s image and
           the packet never said so. The law SET is adequate (L30 kills
           the adversary); the boundary line was missing.
FIXED-BY   this commit. L31's row carries NOTE L31 naming its reach and
           naming L30 as the law a client must cite for an oracle
           guarantee; `badHandleLlm` and its three refutations move
           into the module's `Adversary` namespace, so the boundary
           cannot be relaxed without a red build.
```

The third row is from the RE-ATTACK (`cf91531c`, verdict
STANDS-AMENDED: both holes confirmed closed structurally — the breaker
printed the reduced proof term and traced a planted `sorry` through
both layers to check the primary/corollary inversion was real, not a
renaming). It is the same finding as HOLE-1, found again in the rows
the fix pass did not reach.

```
BROKE      e1ceb205 — the FIX was correct and INCOMPLETE.
LAW        the HOLE-1 correction as this packet applied it: the
           narrowed-primary / ∀-corollary structure, adopted for
           ADQ-INL only, while the amended packet simultaneously
           claimed the ADQ block was "now complete across all three
           definitions the slice touches".
WITNESS    `Prog.inr_unique` kept the original one-shot `rwa` and
           `llmOracleHandler_unique` was adopted in the ∀-form — both
           carrying the exact shape HOLE-1 was about. The breaker
           supplied all four missing declarations kernel-checked:
           `syntactic_hyp_iff_inr`, `inr_unique_one_target`,
           `l30_hyp_iff`, `llmOracleHandler_unique_one_program`
           (`AttackAmended.lean` §C1/§C2 @ `cf91531c`). ADQ-L30's proof
           consumes exactly `A := String` and one program per
           operation; at that instance the hypothesis is equivalent to
           the conclusion, with `Prog.bind_pure_right` playing the role
           `interpret_id` plays on the injection side.
           Nothing false, no adversary admitted — a CONSISTENCY defect
           between what the packet claimed of its own block and what
           two of its three rows carried.
CLASS      claim-scope. And the meta-lesson is the part worth keeping:
           **the first fix was applied where the finding pointed rather
           than where the finding reached.** A defect stated as a fact
           about one declaration ("your ADQ-INL prose overclaims") was
           in truth a fact about a proof shape, and the shape had three
           instances. Fixing the cited instance and declaring the block
           complete is how a corrected packet re-acquires the error it
           just removed.
FIXED-BY   this commit. All four declarations folded in with credit;
           NOTE ADQ states the shape lesson and its uniform
           application; ADQ-SUM's exemption is named and grounded in
           `sum_unique_iff` rather than assumed.
```
