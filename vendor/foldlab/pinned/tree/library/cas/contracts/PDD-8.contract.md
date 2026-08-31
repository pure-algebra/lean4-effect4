# PDD-8 — the contract packet: interpretation's universal property, and the tower's monoid

Ticket: `.staging/wave-2/PDD-8.md`. Process: `.claude/skills/implement/`
(SKILL.md, CONTRACT.md, IMPLEMENTER.md). Owed-ledger item 5 of
`.staging/algebraic-review/THE-ALGEBRA.md` (§2.2, §2.4, §3.3). Authored
before `library/cas/Cas/Backend/Universal.lean` exists and committed
ahead of it, so the history carries the order.

**AMENDED 2026-08-30, fix pass after the independent breaker's verdict**
(`library/cas/contracts/attacks/PDD-8/`, branch
`attack/opus-cc-mac/pdd-8`, commit `6e6fa80a`): STANDS-with-holes — no
BREAK, seven HOLEs, six NOTEs, against packet `8f821ffa` and castle
`6ce34fff`/`8a241313`. Every amendment below is marked at its site and
carries a ledger row at the end. Six of the seven holes are closed with
the breaker's OWN supplied proofs, credited by path and commit at each
adopting declaration; HOLE-2 is not this lane's to close and is recorded
as a ruling owed.

```
CATEGORIES algebraic-laws, lemmas-proofs, abstraction-modules,
           proof-mechanics
```

CATALOG rows opened for those tags (`.claude/skills/implement/CATALOG.md`),
and what each contributed:

- **§6.2 Intrinsic versus Extrinsic Specifications** (`lemmas-proofs,
  algebraic-laws`) — "multi-call algebraic facts are proved
  extrinsically, by induction". Every law below is multi-call
  (uniqueness compares two handlers, existence compares a morphism to an
  interpretation, associativity compares two composites), so none is
  intrinsic to a definition and all of them are separate declarations
  proved by induction on `Prog`. It also supplies the SHAPE of the unit
  and associativity laws that §6 of the castle instantiates for
  `through`.
- **§9.5 Summary** (`abstraction-modules, algebraic-laws`) —
  "abstraction-operation commutation: for each concrete operation there
  is an abstract one with `Abs(opC(c,x)) = opA(Abs(c),x)". Here the
  abstraction function is `interpret` itself: it carries the syntactic
  operations of `Prog S` to the target monad's, and L13 IS that
  commutation square stated once. §9.5's other law —
  representation-independent client proof — is why the packet's
  claim-scope names what a client may NOT unfold: `interpret`'s
  recursion is not the client's business, the four laws are.
- **§9.2 Export Sets** and **§9.1 Module Imports** (`abstraction-modules`)
  — "close the surface over every name the exported material mentions",
  and "imports explicit and hierarchical, never cyclic". Both bite on the
  FILE frame: the castle imports `Cas.Lang.Representation` and nothing
  else, adds no name to any exported ledger, and the placement note in
  its docstring is §9.1's discipline applied to a Lake glob rather than
  to a Lean import.
- **§B.7 Universal Quantification** and **§B.8 Existential
  Quantification** (`proof-mechanics`) — "universals are proved for
  arbitrary; existentials are discharged by exhibiting the witness", and
  §B.7's warning about "an unused variable eliminated over an EMPTY type,
  turning `forall x :: true` into an incorrect claim". That warning is
  the source of falsifier F-ONETYPE below: read at a single answer type,
  L17's hypothesis can be vacuous, because `Prog S Empty` is uninhabited.
  L18 is the existential, and it is discharged by producing the handler,
  not by an argument that one exists.
- **§B.6 Free Variables and Substitution** (`proof-mechanics`) — the
  polymorphic `φ : {A : Type} → Prog S A → M A` is substituted at
  `A := S.Ans op` inside its own `bind_law`; the binder discipline is the
  whole reason the morphism predicate quantifies over types rather than
  fixing one.

## The degree claim

**I have shown algebraically that this can be implemented at the Lean
escalation tier.** Every law below is a Lean statement over the shipped
`Handler` / `interpret` / `Handler.through` / `idHandler` / `run`
declarations, proved to the kernel with no `sorry`, no `native_decide`,
and no new axiom; every falsifier is a formal counter-theorem whose
witness the kernel evaluates.

Axiom census. The first draft's census was verified EXACT by the breaker
(`RESULTS.md`, "the packet's census is exact"), including its count of
four axiom-free declarations. The fix pass grows the module, so that
count is SUPERSEDED and re-measured mechanically — every constant whose
defining module is `Cas.Backend.Universal`, `collectAxioms` on each, not
a hand list:

```
78 public constants (compiler-generated recursors and projections
   included), of which 52 are theorems
axiom sets   44 × []            10 × [Quot.sound]
              6 × [propext]     18 × [propext, Quot.sound]
union        {propext, Quot.sound}
22 of the 52 theorems depend on NO axiom at all
```

No `Classical.choice`, no `sorryAx`, no `Lean.ofReduceBool`, no
declaration of kind `axiom`. `Quot.sound` enters through `funext`
wherever `Handler.ext` is used; `propext` through `simp`. The axiom-free
block is where the falsifiers live — they are computations, which is what
makes them witnesses rather than arguments.

**The escalation gate is named, and it is a NEGATIVE gate.** This slice
adds theorems only. Nothing it proves reaches the host as new bytes, so
`γ` is discharged by byte-identity of every generated surface under
`mise run check:cas` — the claim is "the model gained theorems and the
emitted TypeScript did not move", and a red `--check` refutes it. There
is no host battery because there is no host change; per CONTRACT.md
§Escalation this packet's floor is the Lean statement plus the byte gate,
and it is written down rather than implied.

## Prior art, and what was done with it

`.staging/algebraic-review/handlers-semantics-exhibits.lean` §3–§5 carries
the review's sketches for L16, L17, L18, L34 and L35, kernel-checked at
main `7dac14d8`. The ticket's instruction is "verify, use, cite", so they
were re-elaborated against this worktree's HEAD BEFORE this packet was
written — trusting an uncommitted, gitignored file would be exactly the
provenance failure C6 exists to prevent. Result: **every sketch survives
as written.** One strengthening was found and is taken into the laws
below — the existence sketch (§4) declares `[LawfulMonad M]` and never
uses it, so L18 is stated at a bare `Monad`. That is a strictly stronger
theorem, not a refutation, so it is recorded here and not in the break
ledger.

**Second source, adopted in the fix pass: the independent breaker's
record** (`library/cas/contracts/attacks/PDD-8/Attack.lean`, branch
`attack/opus-cc-mac/pdd-8`, commit `6e6fa80a`), which supplied PROVED
repairs for six of the seven holes it found. Every adopted proof is
credited at its declaration in the castle and named in the ledger row it
closes. The breaker built none of this castle and used no channel to the
builder; the packet and the tree are the only things that crossed.
Adopting an attacker's proof rather than re-deriving it is the honest
move — the work is theirs, the record says so, and re-deriving it would
have hidden that.

## The algebra

Carriers, all shipped, none new:

```
Sig                    Cas/Lang/Sig.lean:13      operations + answer types
Prog S A               Cas/Lang/Prog.lean:25     the free-monad carrier
Handler S M            Cas/Lang/Handler.lean:42  one field: handle
interpret h            Cas/Lang/Handler.lean:47  the induced map
idHandler              Representation.lean:63    every operation means itself
Handler.through        Cas/Lang/Tower.lean:65    the tower's composition
run H fuel             Cas/Lang/Interp.lean:146  the fueled small-step run
```

One piece of statement apparatus, proof stratum only, minting no sort,
kind, or registry row (PDD-2's licence, decision 2):

```
IsMonadMorphism S φ  for  φ : {A : Type} → Prog S A → M A
  pure_law  ∀ a,     φ (Prog.pure a) = pure a
  bind_law  ∀ p f,   φ (p.bind f)    = φ p >>= fun a => φ (f a)
```

It exists because the estate has the two halves in two files
(`interpret_pure`, `Representation.lean:110`; `interpret_bind`,
`Handler.lean:53`) and no declaration naming their conjunction — which is
THE-ALGEBRA L13's complaint — and because it is also the HYPOTHESIS class
L18 needs. One definition, both jobs.

The polymorphism is not decoration: `bind_law` is instantiated at
`A := S.Ans op` inside the induction, so a predicate fixing one `A` would
not prove L18.

```
REQUIRES   `Monad M` for every statement (interpretation needs it to
           exist). Beyond that, each theorem carries EXACTLY the monad
           equation its proof spends, named as an explicit hypothesis:

             LeftUnit M   pure a >>= f = f a
             RightUnit M  x >>= pure = x
             BindAssoc M  (x >>= f) >>= g = x >>= fun a => f a >>= g

             RightUnit             L17 (both forms), L35 left unit,
                                   one_type_can_be_enough
             LeftUnit + BindAssoc  L34, interpret_bind/through re-proofs
             all three             initiality, the pin's inhabitant
             none at all           L12, L18, L16, L35 right unit
             [LawfulMonad M]       L13 only, and only because it reuses
                                   main's `interpret_bind` directly; the
                                   equation-level twin is stated beside
                                   it

           AMENDED, breaker hand (HOLE-3). The first draft said
           "`LawfulMonad M` for exactly three … and where it is required
           it is LOAD-BEARING, which is falsifier F-LAWFUL". That was
           wrong twice. F-LAWFUL shows dropping EVERY hypothesis breaks
           uniqueness; it does not show `LawfulMonad` is the hypothesis
           needed — and it is not, since `LawfulMonad` also bundles
           `LawfulApplicative` and `LawfulFunctor`, which no proof here
           touches. The breaker exhibited targets where the theorems are
           TRUE and the first draft's statements could not even be
           typed: `RUnit` (right unit, no `LawfulMonad` instance) for
           L17 and the left unit, `Ct` (left unit + associativity, no
           instance) for L34. `LawfulMonad` implies all three
           (`leftUnit_of_lawful` and friends), so nothing downstream is
           harder to use.

           Nothing requires anything of `H`: the statements that mention
           an address function (BOUND, and the `runP` shape row) are
           universally quantified over it, per this lane's CAS-003
           discipline.

           There is no starting-word precondition and no run-relative
           reading to preserve: nothing in this slice runs anything
           except the two closed computations of BOUND, whose starting
           word is written into the statement.

ENSURES    Every declaration under contract is a pure function of its
           arguments or a proposition about them. There is no second
           state and `old` is vacuous.

DECREASES  Structural recursion on `Prog S A`, whose `vis` child is the
           continuation applied to an answer (CATALOG §4.3: recurse on
           structurally included children and the decrease is free). No
           new recursion is introduced beyond `phiDrifts`, the F-BIND
           witness, which is structural on the same carrier. No fuel is
           quantified over anywhere: BOUND names its two fuels as
           literals.

FRAME      Reads: the declarations listed under "the algebra". Writes:
           nothing — no state, no store, no address, no byte.

           The FILE frame is the load-bearing half. This slice adds ONE
           new module and edits NO existing file: not `Handler.lean`,
           not `Interp.lean`, not `Tower.lean`, not `Representation.lean`,
           not `lakefile.toml`, not any generated surface. It also adds
           no `Cas.Backend.*` row to `Walk.libraryImports`
           (`tools/Walk.lean:45-55`), so the surface, obligation and law
           ledgers do not move either. CORRECTED, breaker hand
           (NOTE-2): the first draft added "that is what makes the
           negative byte gate a real gate rather than a formality",
           which is false — the byte gate is equally green with this
           module DELETED. See "What the byte gate proves, and what it
           does not" under Gates.
```

## The file frame's one honest cost — where the module lives

The statements are about `Cas/Lang/`. The module is at
`library/cas/Cas/Backend/Universal.lean`, and that is a MECHANICAL
consequence of the fence, disclosed here because a reader who finds a
Lang theorem under `Backend/` deserves to be told why:

- `lake --wfail build` builds a module only if some `[[lean_lib]]` glob
  matches it. The `Cas` library's glob is its root module alone, so a new
  `Cas/Lang/*.lean` that nothing imports is NOT kernel-checked — verified
  empirically, by planting a `sorry` under `Cas/Lang/` and watching
  `--wfail` stay green.
- `Cas.Backend.+` is the only glob in `lakefile.toml` that picks up a new
  module without editing the lakefile, and the ticket's fence forbids
  editing it. The same `sorry` planted under `Cas/Backend/` turns
  `--wfail` red, so the placement buys a real gate.
- `Cas.Backend.*` leaves are named ONE BY ONE in `Walk.libraryImports`,
  and this one is not named, so the module is outside the ledgers'
  environment and moves no byte.

This is the device `Cas/Backend/Canon.lean` (PDD-1) and the `CasWp`
library (PDD-2) already use, taken for the same reason. Promoting the
module into `Cas/Lang/` and into the walk is a promotion, and a promotion
is a ruling — not a side effect of this slice.

## The laws, each with its falsifier

```
LAW  L12  THE UNFOLDING LAW, stated once and generally.
          interpret h (.vis op k)
            = h.handle op >>= fun a => interpret h (k a)
FALS L12  exhibit h, op, k where the two sides differ.
BATT L12  Universal.lean — `interpret_vis`. It is `rfl`; the content of
          the law is that it has a NAME, because today the estate
          restates it locally at each use and generally nowhere
          (THE-ALGEBRA §3.21).

LAW  L13  INTERPRETATION IS A MONAD MORPHISM, as ONE statement.
          IsMonadMorphism S (fun p => interpret h p),
          for every handler into every lawful target.
FALS L13  exhibit h, p, f with
          interpret h (p.bind f) ≠ interpret h p >>= (interpret h ∘ f),
          or h, a with interpret h (.pure a) ≠ pure a.
BATT L13  Universal.lean — `interpret_isMonadMorphism`. The two halves
          are the estate's own `interpret_pure` and `interpret_bind`;
          the declaration is the conjunction those two files do not
          have. `interpret_isMonadMorphism_of_equations` is the same
          statement at `LeftUnit + BindAssoc`, for targets with no
          `LawfulMonad` instance (added in the fix pass).

LAW  L16  HANDLER EXTENSIONALITY.
          (∀ op, h.handle op = g.handle op) → h = g
FALS L16  exhibit h ≠ g agreeing on every operation.
BATT L16  Universal.lean — `Handler.ext`.

LAW  L17  UNIQUENESS. interpret h = interpret g → h = g, in two forms:
          SHARP  (∀ op, interpret h (Prog.op op)
                          = interpret g (Prog.op op)) → h = g
          FULL   (∀ A p, interpret h p = interpret g p) → h = g
FALS L17  exhibit h ≠ g whose interpretations agree everywhere.
BATT L17  Universal.lean — `handler_eq_of_interpret_op_eq`,
          `handler_eq_of_interpret_eq`, both at `RightUnit M`
          (AMENDED, HOLE-3), plus `l17_holds_over_runit` as the
          sufficiency witness at a target with no `LawfulMonad`
          instance.
NOTE L17  The FULL form is spelled at every answer type because
          `interpret h` is not one function (`A` is implicit). The
          first draft justified that by F-ONETYPE's headline, which is
          false; the true motive is that answer types VARY WITH THE
          OPERATION, so no single `A` is the right carrier for a
          general `S`. See the amended F-ONETYPE.

LAW  L18  EXISTENCE. Every monad morphism out of `Prog S` IS an
          interpretation, and the handler is recovered from the
          morphism's own action on single operations:
          IsMonadMorphism S φ →
            ∀ p, φ p = interpret ⟨fun op => φ (Prog.op op)⟩ p
          and hence ∃ h, ∀ A p, φ p = interpret h p.
FALS L18  exhibit φ satisfying both morphism laws and a program p with
          φ p ≠ interpret h p for EVERY handler h — equivalently, for
          the one handler L18 names, since L17 says there is no other
          candidate.
BATT L18  Universal.lean — `interpret_of_isMonadMorphism`,
          `exists_handler_of_isMonadMorphism`.
NOTE L18  Stated at a bare `Monad M`. The review's §4 sketch declares
          `[LawfulMonad M]` and does not use it; verification found
          that and the hypothesis is dropped.

LAW  UP   FREENESS — L16 + L17 + L18 together. Every monad morphism
          out of `Prog S` is induced by EXACTLY ONE handler; i.e.
          `interpret` is a bijection `Handler S M ≃ Mor(Prog S, M)`.
FALS UP   exhibit a morphism induced by two different handlers, or by
          none.
BATT UP   Universal.lean — `prog_is_free`, with `existsUnique_handler`
          kept as an alias so this row and the old prose still resolve.
NOTE UP   AMENDED, breaker hand (HOLE-1). The first draft called this
          theorem "`Prog S` is INITIAL". It is not. `Prog S` admits TWO
          distinct monad morphisms into `StateT Nat Id`
          (`prog_is_not_initial_among_monads`, Attack.lean §4a), so it
          is not initial in monads-and-monad-morphisms — the only
          category this packet's vocabulary names, since
          `IsMonadMorphism` is the only morphism notion in it. The word
          for the theorem is FREENESS, and `Lang.lean:21`'s "free monad
          of continuations over a signature" is the citation it
          discharges cleanly. `EFFECTS-BACKEND.md:263`'s "INITIAL" is a
          separate matter — see the claim-scope section and HOLE-2.

LAW  INIT INITIALITY, in the category where it holds. In `S`-MODELS —
          objects `(M, h)`, morphisms the monad morphisms respecting the
          chosen meanings — `(Prog S, idHandler)` is initial: for every
          monad and every handler there is EXACTLY ONE monad morphism
          out of `Prog S` sending each operation to its handled
          meaning, and it is `interpret h`.
FALS INIT exhibit a monad and handler admitting two such morphisms, or
          none.
BATT INIT Universal.lean — `prog_is_initial_in_S_models`, the breaker's
          own proof (Attack.lean §4b), restated at the three equations
          rather than `[LawfulMonad M]`.
NOTE INIT The quantifier order IS the difference, and it is why UP does
          not deliver this: freeness fixes a MORPHISM and produces a
          unique HANDLER; initiality fixes a HANDLER and produces a
          unique MORPHISM. Inter-derivable, and only one of them was in
          the first draft.

LAW  PIN  ADEQUACY — the property pins `interpret`, it does not merely
          admit it. Any operator I : Handler S M → ∀ {A}, Prog S A → M A
          such that (a) every `I h` is a monad morphism and (b)
          I h (Prog.op op) = h.handle op, satisfies I h p = interpret h p
          at every h, A and p.
FALS PIN  exhibit a wrong-but-passing interpreter: an I satisfying (a)
          and (b) that disagrees with `interpret` somewhere.
BATT PIN  Universal.lean — `interpret_pinned`. This is the obligation
          class the whole process turns on ("is Q strong enough that no
          wrong implementation passes?"), and it is discharged rather
          than argued: there is NO wrong-but-passing interpreter.
NOTE PIN  AMENDED, breaker hand (HOLE-6), three ways.
          (i) The pin's class is EMPTY at some targets, and "no
          wrong-but-passing interpreter" is then true only because
          there is no interpreter at all —
          `interpret_pinned_is_vacuous_over_collapse` (Attack.lean §7
          F1) exhibits it at `Collapse`, the very target F-LAWFUL uses.
          (ii) The first draft's anti-vacuity companion carried
          `[LawfulMonad M]` while the pin carried `[Monad M]`, so it
          vouched for only part of the pin's own quantifier. It is
          restated at the three equations —
          `interpret_inhabits_the_pin`, strictly wider than
          `LawfulMonad` and exactly the condition making `interpret`
          satisfy the pin's hypotheses. `interpret_satisfies_the_property`
          is kept as its alias.
          (iii) The pin's OWN hypotheses were never falsified, though
          this packet applies that discipline to L17 and L18. Both drops
          fire, and both are the breaker's: `pinned_needs_op_agreement`
          (a morphism at every handler that IGNORES the handler) and
          `pinned_needs_the_morphism_law` (agrees with every handler on
          every single operation and is not `interpret`).

LAW  L34  `through` IS ASSOCIATIVE.
          (t.through u).through h = t.through (u.through h)
FALS L34  exhibit t, u, h and an operation where the two composites
          disagree.
BATT L34  Universal.lean — `through_assoc` at `LeftUnit + BindAssoc`
          (AMENDED, HOLE-3), over `interpret_through_of_equations` —
          L33 re-proved at the equations it spends, because main's
          `interpret_through` is stated at `[LawfulMonad M]`.
          `through_assoc_over_ct` is the witness that the weakening is
          real: associativity over `Ct`, which has no `LawfulMonad`
          instance.

LAW  L35  `idHandler` IS A TWO-SIDED UNIT for `through`.
          t.through idHandler = t   and   idHandler.through h = h
FALS L35  exhibit t (or h) and an operation where either unit law
          fails.
BATT L35  Universal.lean — `through_id_right` (no hypothesis at all:
          the target is `Prog T`), `through_id_left` at `RightUnit M`
          (AMENDED, HOLE-3 — the proof is that equation, once), and
          `through_id_left_over_runit` as the witness that the
          weakening is real.

LAW  MON  THE TOWER IS A MONOID, at the carrier where it is one:
          `Handler S (Prog S)` under `through`, with `idHandler` as
          unit — associativity and both unit laws at that one carrier.
FALS MON  exhibit three endo-handlers whose two bracketings differ, or
          one for which a unit law fails.
BATT MON  Universal.lean — `through_monoid`.
NOTE MON  The honest scope, stated here and not discovered later:
          `through` is a binary operation only on the ENDOMORPHISMS at
          one signature. Across signatures the same three facts are a
          CATEGORY (objects: signatures), and `through_assoc` is stated
          in that generality. Neither gives the tower a bottom — L37
          (`Handler ByteSig M`) is still owed, so "interpretation
          composes all the way down" stays a pending word.

LAW  BOUND  THE BOUNDARY — at a fixed fuel there is NO composition law
            on run-results at all: `run H f (p.bind g)` is not a
            FUNCTION of `run H f p` and `run H f ∘ g`. So `run H f` is
            not a monad morphism out of `Prog CasSig` under ANY monad
            structure on its codomain, and the obstruction is
            well-definedness rather than a choice of `bind`.
FALS BOUND  exhibit a composition law making `run H f` a monad morphism
            — i.e. show `run H f (p.bind g)` IS determined by
            `run H f p` and `run H f ∘ g`.
BATT BOUND  Universal.lean — `run_has_no_composition_law`, the
            breaker's own proof (Attack.lean §5c), over
            `run3_load_once_eq_twice`: at fuel 3, one load and two loads
            are the SAME run at EVERY word, and binding a third load
            separates them. Universally quantified over `H`, the
            address and the node.
NOTE BOUND  AMENDED, breaker hand (HOLE-5). The first draft's battery,
            `run_fixed_fuel_is_not_compositional`, computed ONE
            composite that outruns its parts. That is evidence for the
            law, not the law — determination is refuted by TWO programs
            with the same run whose composites differ, and the first
            draft had one program. The theorem is kept, RENAMED to what
            it proves (`run_composite_outruns_its_parts`); the law is
            the breaker's.
```

### The falsifiers this packet keeps as live theorems

Three hypotheses could be read as decoration. Each is refuted by a
witness the kernel computes, and each witness stays in the tree so the
hypothesis cannot be quietly relaxed later.

```
F-LAWFUL   L17 needs SOME hypothesis on the target.
           AMENDED, breaker hand (HOLE-3): the first draft's headline
           was "L17's `LawfulMonad M` is load-bearing", which this
           witness does not show. It separates "no hypothesis" from
           "some hypothesis" and says nothing about which — `Collapse`
           fails `RightUnit` too. The hypothesis L17 actually needs is
           `RightUnit`, and `l17_holds_over_runit` is the other side.
WITNESS    M := fun _ => Bool with the degenerate, deliberately
           UNLAWFUL structure `pure _ := true`, `bind _ _ := true`.
           Every program interprets to `true` under every handler, so
           ⟨fun _ => true⟩ and ⟨fun _ => false⟩ over the one-operation
           signature have equal interpretations at every type and are
           visibly different handlers.
           The axiom it violates is now NAMED and proved rather than
           asserted: `LawfulMonad.pure_bind` (`collapse_not_lawful`,
           the breaker's proof, Attack.lean §3c).
BATTERY    Universal.lean — `uniqueness_needs_lawful`,
           `collapse_not_lawful`, `l17_holds_over_runit`.

F-ONETYPE  There EXISTS an answer type at which agreement is vacuous.
           AMENDED, breaker hand (HOLE-4). The first draft's headline
           was "L17 read at ONE answer type proves nothing", and that
           is FALSE at the falsifier's own signature: at `OneSig`,
           agreement at the single answer type `Unit` forces handler
           equality outright, because `Prog.op op : Prog OneSig Unit`
           (`one_type_can_be_enough`, Attack.lean §3d, adopted). What
           the theorem in the tree has always proved is the amended
           headline — ONE BADLY CHOSEN type proves nothing.
WITNESS    `Prog S Empty` is UNINHABITED when every operation's answer
           type is inhabited — a program must eventually `pure`, and
           there is nothing to `pure`. So "∀ p : Prog S Empty, …" is
           vacuously true of any two handlers. CATALOG §B.7's empty-type
           warning, instantiated in the estate's own carrier.
BATTERY    Universal.lean — `single_type_agreement_is_not_enough`, and
           `one_type_can_be_enough` beside it as the counter-witness
           that forced the amendment.

F-BIND     L18's `bind_law` is load-bearing; `pure_law` alone is not
           enough.
WITNESS    `phiDrifts h g` — handle the FIRST operation with `g` and
           everything after it with `h`. It satisfies `pure_law`, it
           agrees with `interpret g` on every SINGLE operation (so L18
           would read off the SAME handler), and at a two-operation
           program over `StateT Nat Id` it answers `((), 1)` where
           `interpret hNop` answers `((), 0)`. Two maps, one induced
           handler, different values: the conclusion cannot hold for
           both. This is a realistic wrong implementation — an
           interpreter that installs one semantics for the head
           operation and another for the tail — not a pathology.
BATTERY    Universal.lean — `bind_law_is_load_bearing`, and — ADDED on
           breaker NOTE-4 — `phiDrifts_pure_law` and
           `phiDrifts_read_off`, the two premises the first draft
           asserted in prose and did not state. Without the second the
           disagreement at `twoOps` is a coincidence rather than a
           refutation: the falsifier's force is that L18 reads the SAME
           handler off both maps.

F-PIN-OP   The pin's operation-agreement hypothesis is load-bearing.
           ADDED, breaker hand (HOLE-6): this packet applied the
           drop-a-hypothesis discipline to L17 and L18 and not to the
           pin.
WITNESS    `IIgnores` — an operator that is a morphism at every handler
           and IGNORES the handler it is given.
BATTERY    Universal.lean — `pinned_needs_op_agreement` (breaker's
           proof, Attack.lean §7 F2).

F-PIN-MOR  The pin's morphism hypothesis is load-bearing.
WITNESS    `IDrifts` — agrees with every handler on every single
           operation, and is not `interpret`.
BATTERY    Universal.lean — `pinned_needs_the_morphism_law` (breaker's
           proof, Attack.lean §7 F2).

F-PIN-EMPTY  The pin's hypothesis class is EMPTY at some targets.
WITNESS      At `Collapse`, `bind_law` forces every `I h (Prog.op op)`
             to `true` and operation-agreement then demands
             `hFalse.handle () = true`. Nothing satisfies the pin there.
BATTERY      Universal.lean — `interpret_pinned_is_vacuous_over_collapse`
             (breaker's proof, Attack.lean §7 F1). This is a scope
             statement, not a defect in the pin: the pin is true and
             informative exactly where `interpret_inhabits_the_pin`
             applies.
```

## Claim-scope — what these theorems do NOT say

The anti-overclaim class, written before the proofs so it cannot be
written to fit them; the fix pass's amendments are marked at each site
and carry ledger rows.

**Not claimed: initiality among monads.** AMENDED, breaker hand
(HOLE-1). `Prog S` is NOT initial in monads-and-monad-morphisms — it
admits two distinct monad morphisms into `StateT Nat Id`. The theorem
LAW UP proves is FREENESS, a hom-set bijection; the initiality that
holds is LAW INIT, in `S`-models, and it is a different theorem with the
quantifiers the other way round. The first draft asserted one and
delivered the other.

**A RULING IS OWED, and it is not this lane's to make** (HOLE-2). The
first draft said LAW UP is "the theorem `EFFECTS-BACKEND.md:263`'s
'INITIAL' … was naming". That line's own parenthetical binds INITIAL to
`eq_of_forall_interpret` — the declaration this packet says it is NOT —
and `eq_of_forall_interpret` is neither freeness nor initiality but
faithfulness of the syntactic semantics (`interpret_id` specialized at
`idHandler`). The estate therefore carries THREE readings of one word:

```
faithfulness   eq_of_forall_interpret   (R14's own gloss, :263)
freeness       prog_is_free             (LAW UP, landed here)
initiality     prog_is_initial_in_S_models (LAW INIT, landed here)
```

Which reading R10/R14's "INITIAL" binds to is an OPERATOR RULING. This
lane touches nothing in `EFFECTS-BACKEND.md` and withdraws the claim
that it discharges that line's word. `Lang.lean:21`'s "free monad" is
the one citation this lane discharges cleanly, and it is discharged.
Record: `contracts/attacks/PDD-8/RESULTS.md` HOLE-2.

**The boundary the ticket names: the semantics THE-ALGEBRA §3.4 found
outside the handler algebra — and it is NOT the estate's whole
boundary.** AMENDED, breaker hand (HOLE-7). The first draft presented
this enumeration as THE boundary and nowhere declared it partial. It is
the REVIEW's three; two more semantics live in this repository and are
added below, and nothing here claims even the amended list is complete.
R10 rules that a semantics IS a handler. This packet proves the form of
that claim and, for each semantics outside it, says exactly what the
proof does and does not reach:

- **`Prog.handleLlm`** (`Interp.lean:184-187`) is a map
  `Prog AgentSig A → Prog CasSig A`, so it is of the right SHAPE and L18
  reaches it — **conditionally**. The condition is `bind_law`, which is
  precisely the judgment `Interp.lean:19, 181-183` asserts ("interpret …
  by monad morphism") and nothing on main proves. So the honest reading
  of L18 here is "IF `handleLlm` respects `bind`, THEN some handler
  induces it" — and L18 promises a handler, it does not COMPUTE the
  estate's intended one. Discharging the hypothesis (L32) and exhibiting
  `idHandler.sum ⟨fun (.infer q) => .pure (oracle q)⟩` as the handler
  (L30) are PDD-7's, and this packet claims neither.
- **`stepRooted`** (`Roots.lean:69-81`), and with it `step`, `run` and
  `runRooted`, are outside — for a reason that is not the one the first
  draft gave. **WITHDRAWN, breaker hand (HOLE-5):** "they are not maps
  `Prog S A → M A` at all" is FALSE. `Status CasSig` is a
  `Type → Type`, so `RunM := fun A => Word → Status CasSig A × Word` is
  one, both families type-check against it, and it even carries a
  `Monad` instance — `runAsMap` and `stepAsMap` in the castle are the
  refutation, and they are the breaker's definitions. The continuation
  does not leave the shape; it lands in `Status CasSig A`, indexed by
  the same `A`.
  The REAL reason is LAW BOUND: at a fixed fuel there is no composition
  law at all. The correction is not cosmetic — "wrong shape" would put
  the operational semantics outside the property FOREVER, while "no
  composition law at fixed fuel" is a fact about a fuel discipline, and
  that is the right diagnosis because `runP` below is a FUEL-FREE run
  that is still outside. What relates these to the denotational side is
  the bridge already on main (`run_interpretRef_agree`,
  `Handler.lean:255`), whose fuel is EXISTENTIAL for exactly this
  reason; nothing here supplants it, and `runRooted`'s zero laws
  (THE-ALGEBRA §3.4b) stay zero.
- **`replayHandler`** (`Handler.lean:279-292`) IS a handler, hence a
  semantics by this file's theorem — and it is still the wrong one. The
  universal property constrains FORM, not CONTENT: being an
  interpretation says nothing about being the INTENDED interpretation.
  The review's two kernel-checked witnesses (THE-ALGEBRA §3.4c: replay
  starves on a duplicate, and refuses a load the reference admits) are
  untouched by anything here, and ruling Q4 stays owed. A reader who
  takes "a semantics IS a handler" as reassurance about `replayHandler`
  has read this packet backwards.
- **`Cas.Lang.runP`** (`Defun.lean:293`) — ADDED, breaker hand
  (HOLE-7). The direct interpreter of the defunctionalized table, and
  the semantics the emitter's gate actually EXECUTES. Its domain is
  `PProg`, not `Prog S A`, so it is neither a handler nor a map out of
  `Prog`; and the fueled-run reason above does not reach it, because
  `runP_halts` (already on main) proves it NEVER reports `.running`. A
  total semantics of store programs, outside the property for a third
  reason the first draft did not name. Shape witness in the castle:
  `runPShape`, `runP_never_running`.
- **`Cas.Lang.wp` / `Cas.Lang.wlp`** (`Wp.lean:150,154`, PDD-2's castle,
  landed in this same wave) — ADDED, breaker hand (HOLE-7).
  CONTRAVARIANT: postconditions to preconditions, so not of the shape
  `Prog S A → M A` for any `M`, and no reading of R10 reaches it. The
  first draft's obligation-class line honours the WLP/WP distinction and
  then failed to place the estate's own WLP/WP transformer against the
  property being scoped. Shape witnesses: `wpShape`, `wlpShape`.

The rest of the boundary:

- **Not claimed: anything about the sum algebra.** `Handler.sum`,
  `Prog.inl`/`inr` and L21–L31 are PDD-7's. Nothing here is stated over
  a signature sum, and the one-operation signatures used by the
  falsifiers are not sums.
- **Not claimed: a bottom for the tower.** MON is a monoid at one
  signature; `Handler ByteSig M` does not exist (THE-ALGEBRA L37), so
  `EFFECTS-BACKEND.md:213-216`'s "interpretation composes all the way
  down to the admitted seams" remains the pending word §3.6 named it.
- **Not claimed: that `ObsEq` is `=`.** UP is about morphisms out of
  `Prog S`, not about program equality. THE-ALGEBRA §3.3's refutation
  stands: `ObsEq` is strictly COARSER than structural equality, its
  witness is `put n` against `put n >>= fun a => put n >>= fun _ =>
  pure a`, and nothing here narrows it.
- **Not claimed: anything about host code.** No TypeScript is a proof
  subject; nothing moves a generated byte or adds a word-equality
  vector. No soundness word attaches to any host seam (estate C5,
  R14 strata 3–4).
- **Not claimed: that `IsMonadMorphism` is estate vocabulary.** It is
  statement apparatus in the proof stratum of one leaf module, minting
  no sort, kind, or registry row. Promoting it — into `Cas/Lang/`, into
  `Walk.libraryImports`, into CONTEXT.md — is a ruling.
- **Not claimed: that this module is in the library's ledgers.** It is
  outside `Cas`'s import closure and outside `Walk.libraryImports`, so
  it is invisible to the surface, obligation and law ledgers. That is
  exactly why the "moves no bytes" gate holds, and it is written here
  rather than left in the lakefile (PDD-2's NOTE-2, adopted in advance).
- **Not claimed: universe generality — and the consequence, drawn.**
  Every statement is at `A : Type`, the universe `Handler`'s
  `M : Type → Type v` forces, while `Prog S A` is polymorphic in
  `A : Type u`. SHARPENED on breaker NOTE-5: the consequence the first
  draft left undrawn is that there are programs no handler can
  interpret — not "not yet", but not at the shipped `Handler`.
  `bigProg : Prog OneSig Type` is one. For such programs R10's "a
  semantics IS a handler" is not merely unproved; they have NO handler
  semantics at all.
- **Not claimed: that L18's bare `Monad` reaches every monad.**
  RECORDED on breaker NOTE-1. `IsMonadMorphism` is SELF-LAWFULIZING —
  its `bind_law`, instantiated against `Prog.bind_pure_right` and
  `Prog.bind_assoc'`, drags the monad laws onto the morphism's own
  image over any `M` (Attack.lean §2a). The drop is still real: `Ct`
  has no `LawfulMonad` instance and carries a non-constant morphism out
  of `Prog` (Attack.lean §2b, adopted here for L34's witness). And it is
  not free: `Shift`, the writer monad whose `pure` costs one, admits NO
  morphism out of `Prog S` at all, because the image right-unit law
  forces `n = n + 1` (Attack.lean §2c). "Bare `Monad`" is a proper
  subclass on both sides.

## Obligation classes in play

`algebraic-laws`/`abstraction` (L13 is the commutation square over
`interpret` as the abstraction function; L34/L35/MON are the unit and
associativity axes), `adequacy` (LAW PIN, discharged where its class is
inhabited — there is no wrong-but-passing interpreter — plus six live
falsifiers: F-LAWFUL, F-ONETYPE, F-BIND, F-PIN-OP, F-PIN-MOR,
F-PIN-EMPTY), `claim-scope` (the section above, and LAW BOUND, which is
a claim-scope obligation promoted to a theorem), `termination`
(structural recursion on `Prog`; no fuel is quantified over),
`conformance` (the negative byte gate).

The class that fired on review is `claim-scope`, seven times, and not
once on a false law: every theorem of `6ce34fff`/`8a241313` reproduced.
The defects were in what the module said about its own reach — a word
attached to the wrong theorem, hypotheses stronger than their proofs, a
falsifier headline wider than its witness, a boundary reason that was
false, an adequacy pin paired with a companion that did not cover it,
and an enumeration that read complete and was not.

The `domain`, `contract`, `frame`, `invariant` and `loops` classes
generate nothing and are therefore not written: there is no partial
operation, no two-state postcondition, no mutable state, no represented
structure with an invariant, and no loop.

## Gates

```
lake --wfail build              (from library/cas) — green, no sorry
mise run check:cas              — every byte-identity gate unchanged
git status --short              — empty
```

### What the byte gate proves, and what it does not

The first draft wrote, of the file frame: "That is what makes the
negative byte gate a real gate rather than a formality." That sentence
is CORRECTED here, in the breaker's own words, which are the strongest
statement of the promotion argument this lane has produced. NOTE-2 of
`contracts/attacks/PDD-8/RESULTS.md`, verbatim:

> The packet: "That is what makes the negative byte gate a real gate
> rather than a formality."
>
> Probe: `Cas/Backend/Universal.lean` was MOVED OUT OF THE TREE entirely
> and `mise run --force check:cas` was re-run. It is fully green — every
> byte-identity gate, every self-test, exit 0. The byte gate is a gate
> against DRIFT in what is emitted; it says nothing about whether the
> castle exists or what it proves, because the module is deliberately
> outside `Walk.libraryImports` and outside every emitter's environment.
>
> The only mechanism that binds the castle is `lake --wfail build`,
> which does fire on a planted `sorry` (verified above) — and which is
> equally green when the file is absent. Nothing in the estate's gate
> set would notice this module's deletion. That is a property of the
> placement device the packet chose, not a defect in the packet's
> honesty, and it is the strongest argument for the promotion the packet
> defers: a theorem nobody's ledger knows about is a theorem the estate
> cannot be said to hold.

Two facts stand beside it, both the breaker's and both verified:

- **NOTE-3.** The placement rationale is honest and was verified BOTH
  ways: a `sorry` planted in a new, unimported `Cas/Lang/*.lean` leaves
  `--wfail` green and produces no job at all; the same `sorry` in
  `Cas/Backend/Universal.lean` turns it red. The `Cas.Backend.+` glob
  buys a real gate for what is IN the file.
- **NOTE-6.** Nothing blocks the promotion on names: `Handler.ext`,
  `interpret_vis` and `IsMonadMorphism` are declared in `Cas.Lang` and
  none already exists there (`Auth.lean:387`'s `interpret_vis_state` is
  a distinct name). Promotion into `Cas/Lang/` and into
  `Walk.libraryImports` would move the surface, obligation and law
  ledgers — which is the ruling, and it is still owed.

## Breaks

The ledger was committed EMPTY at `8f821ffa` with the note that the
breaker's pass fills it or leaves it empty on the record. The pass came
back **STANDS-with-holes: no BREAK, seven HOLEs, six NOTEs**. No law is
false and no theorem failed to reproduce, so no BREAK row is owed. Seven
claim-scope/adequacy rows are, and they are entered here.

Common provenance for every row below:

```
RECORD     library/cas/contracts/attacks/PDD-8/{Attack.lean,RESULTS.md}
BRANCH     attack/opus-cc-mac/pdd-8   COMMIT 6e6fa80a
AGAINST    packet 8f821ffa, castle 6ce34fff + 8a241313
BREAKER    independent; did not build this castle
```

```
BROKE      6ce34fff — a word attached to a theorem that does not
           support it.
LAW        `existsUnique_handler`'s docstring and §5 prose: "**`Prog S`
           is initial**: every monad morphism out of it is induced by
           exactly ONE handler"; "With L17 that is INITIALITY".
WITNESS    prog_is_not_initial_among_monads (Attack.lean §4a) — two
           DISTINCT monad morphisms out of `Prog OneSig` into
           `StateT Nat Id`, `interpret hInc` and `interpret hNop`,
           separated at state 0 by ((),1) against ((),0). An initial
           object admits exactly one morphism to each object, and
           `IsMonadMorphism` is the only morphism notion the file
           defines, so the category the reader is handed is
           monads-and-monad-morphisms.
CLASS      claim-scope — the theorem is a hom-set bijection, which is
           FREENESS; the gloss asserted initiality and delivered
           freeness.
FIXED-BY   this fix pass. LAW UP is renamed FREENESS
           (`prog_is_free`, alias `existsUnique_handler` kept); the
           initiality that IS true is landed as LAW INIT
           (`prog_is_initial_in_S_models`), the breaker's own proof,
           with both categories named at their statements.
```

```
BROKE      8f821ffa — a pending word discharged against a line that
           binds it elsewhere.
LAW        packet LAW UP: "This is the theorem
           `EFFECTS-BACKEND.md:263`'s 'INITIAL' … [was] naming… It is
           NOT `eq_of_forall_interpret`."
WITNESS    documentary, `EFFECTS-BACKEND.md:262-265`: the cited line's
           own parenthetical reads "INITIAL (`eq_of_forall_interpret`:
           agreement under every lawful interpretation IS structural
           equality)" — binding the word to the declaration the packet
           says it is NOT. And `eq_of_forall_interpret` is neither
           freeness nor initiality: it is `interpret_id` specialized at
           `idHandler`, i.e. faithfulness.
CLASS      claim-scope.
FIXED-BY   NOT FIXED, and not this lane's to fix. The estate now
           carries three readings of one word (faithfulness, freeness,
           initiality) and binding it is an OPERATOR RULING. The claim
           to discharge `:263` is WITHDRAWN in claim-scope;
           `EFFECTS-BACKEND.md` is untouched. RULING OWED.
```

```
BROKE      6ce34fff — hypotheses stronger than their proofs, by this
           packet's own standard.
LAW        packet REQUIRES: "`LawfulMonad M` for exactly three: L13,
           L17 and `through_id_left` — and where it is required it is
           LOAD-BEARING, which is falsifier F-LAWFUL, not a remark."
WITNESS    uniqueness_from_right_unit, RUnit, runit_right_unit,
           runit_not_lawful, l17_holds_where_the_castle_cannot_state_it,
           through_id_left_over_runit (Attack.lean §3c);
           through_assoc_holds_over_collapse (§7 F3);
           collapse_not_lawful (§3c).
           L17's proof reaches `interpret_op`, whose proof spends ONE
           equation, `x >>= pure = x`. Over `RUnit` — right unit, no
           `LawfulMonad` instance — uniqueness and the tower's left unit
           are TRUE and the packet's statements cannot be TYPED.
CLASS      claim-scope — and self-inconsistency: the packet applied
           "drop what the proof does not use" to the review's
           `[LawfulMonad M]` on L18 and not to the three it wrote
           itself.
FIXED-BY   this fix pass. `LeftUnit`/`RightUnit`/`BindAssoc` are named;
           L17 (both forms), L35's left unit and
           `one_type_can_be_enough` take `RightUnit`; L34 takes
           `LeftUnit + BindAssoc` over re-proofs of `interpret_bind`
           and `interpret_through`; `leftUnit_of_lawful` and friends
           bridge from `LawfulMonad`. Sufficiency witnesses
           `l17_holds_over_runit`, `through_id_left_over_runit`,
           `through_assoc_over_ct` land with them, and
           `collapse_not_lawful` names the axiom F-LAWFUL's witness
           violates.
```

```
BROKE      8f821ffa — a falsifier headline wider than its witness.
LAW        packet F-ONETYPE: "L17 read at ONE answer type proves
           nothing", and the castle docstring "This is why
           `handler_eq_of_interpret_eq` quantifies over `A`".
WITNESS    one_type_can_be_enough (Attack.lean §3d) — at `OneSig`, the
           signature the falsifier itself is built on, agreement at the
           single answer type `Unit` forces handler equality outright,
           because `Prog.op op : Prog OneSig Unit`.
CLASS      claim-scope — the theorem is right; the law line generalized
           past it.
FIXED-BY   this fix pass. F-ONETYPE is restated as "there EXISTS an
           answer type at which agreement is vacuous"; the true motive
           for quantifying over `A` (answer types vary with the
           operation) replaces the false one; `one_type_can_be_enough`
           is adopted and sits beside the theorem it corrects.
```

```
BROKE      6ce34fff — a boundary theorem that does not state its own
           name, and a false reason for the boundary.
LAW        castle §7(b) and module docstring: `step`/`run`/`stepRooted`/
           `runRooted` "are not maps `Prog S A → M A` at all"; and
           packet FALS BOUND, "show `run H f (p.bind g)` IS determined
           by `run H f p` and `run H f ∘ g`", answered by
           `run_fixed_fuel_is_not_compositional`.
WITNESS    RunM with its `Monad` instance, runAsMap, stepAsMap
           (Attack.lean §5b) — the definitions type-check, which IS the
           refutation of the shape reason;
           run3_load_once_eq_twice and run_has_no_composition_law (§5c)
           — at fuel 3 one load and two loads are the same run at every
           word, and binding a third separates them, killing every
           candidate composition law at once.
CLASS      claim-scope (the reason) and adequacy (the theorem proved
           less than the law it was the battery for).
FIXED-BY   this fix pass. The shape reason is WITHDRAWN and its
           refutation adopted; `run_has_no_composition_law` becomes the
           battery for LAW BOUND; the old theorem is kept and RENAMED
           `run_composite_outruns_its_parts`, which is what it proves.
           The corrected reason matters: "no composition law at fixed
           fuel" is a fact about a fuel discipline, and `runP` is a
           fuel-free run that is still outside.
```

```
BROKE      8a241313 — the anti-vacuity commit does not cover the pin it
           vouches for.
LAW        `interpret_pinned` at `[Monad M]` paired with
           `interpret_satisfies_the_property` at `[Monad M]
           [LawfulMonad M]`; packet LAW PIN, "there is NO
           wrong-but-passing interpreter".
WITNESS    interpret_pinned_is_vacuous_over_collapse (Attack.lean §7
           F1) — at `Collapse`, `bind_law` forces every
           `I h (Prog.op op)` to `true` and operation-agreement then
           demands `hFalse.handle () = true`, so the pin's hypothesis
           class is EMPTY there and the adequacy statement is true only
           vacuously. Plus pinned_needs_op_agreement and
           pinned_needs_the_morphism_law (§7 F2) — both of the pin's
           own hypotheses fire when dropped, and neither was falsified.
CLASS      adequacy and claim-scope.
FIXED-BY   this fix pass. The companion is restated at the three
           equations as `interpret_inhabits_the_pin` (alias
           `interpret_satisfies_the_property` kept) — strictly wider
           than `LawfulMonad`, and exactly the condition under which
           `interpret` satisfies the pin; the vacuity witness and both
           hypothesis falsifiers are adopted as F-PIN-EMPTY, F-PIN-OP
           and F-PIN-MOR.
```

```
BROKE      8f821ffa — an enumeration that reads complete and is not.
LAW        packet claim-scope: "for each of the three semantics the
           review found outside it, says exactly what the proof does and
           does not reach", presented as THE boundary and nowhere
           declared partial.
WITNESS    runPShape, runP_is_not_a_fuelled_run, wpShape, wlpShape
           (Attack.lean §6). `runP` (`Defun.lean:293`) is a TOTAL
           semantics whose domain is `PProg`, and the packet's reason
           for excluding fueled runs — "a fueled run reports
           `.running`" — does NOT apply, because `runP_halts` proves it
           never does. `wp`/`wlp` (`Wp.lean:150,154`, PDD-2's castle in
           this same wave) are CONTRAVARIANT and outside by shape; the
           packet names the WLP/WP distinction as a class it honours and
           then does not place the estate's own transformer against the
           property.
CLASS      claim-scope — R10 is a ruling, and the boundary is what tells
           a reader how far it reaches.
FIXED-BY   this fix pass. The enumeration is declared to be THE REVIEW's
           three and not the estate's all; `runP` and `wp`/`wlp` are
           added as rows (d) and (e) with their shape witnesses adopted;
           and no completeness is claimed for the amended list either.
```

### Not breaks, recorded so they are not mistaken for breaks

- The review's existence sketch
  (`handlers-semantics-exhibits.lean` §4, `interpret_of_morphism`)
  carries a `[LawfulMonad M]` hypothesis its proof never uses. TRUE as
  written, merely weaker than the theorem it proves. L18 is stated
  without it. The breaker attacked this drop as possibly hollow and
  FAILED (Attack.lean §2, NOTE-1); the honest reading of the drop is
  now in claim-scope.
- Seven of the breaker's attack families failed outright and are earned
  confidence, not defects: the falsifier triad re-elaborates from
  apparatus re-declared outside this module; no wrong-but-passing
  interpreter exists over a lawful target; `through_id_right`,
  `through_monoid` and `Handler.ext` have nothing to exhibit against;
  the axiom census was exact; the file frame and commit order hold.
  Record: `RESULTS.md`, "Failed attempts".
