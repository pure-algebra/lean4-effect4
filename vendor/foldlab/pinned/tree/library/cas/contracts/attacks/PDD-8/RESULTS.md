# PDD-8 — the breaker's verdict

Adversarial record against the PDD-8 contract packet
(`library/cas/contracts/PDD-8.contract.md`, commit `8f821ffa`) and the
castle it specifies (`library/cas/Cas/Backend/Universal.lean`, commits
`6ce34fff` and `8a241313`). The machine-checked half is `Attack.lean`
beside this file.

```
BREAKER    independent; did not build this castle
SUBJECT    8a241313  PDD-8: close the vacuity reading of the adequacy pin
CASTLE     6ce34fff  PDD-8: the universal property proved — a semantics
                     IS a handler, and the tower is a monoid
PACKET     8f821ffa  PDD-8: the contract packet — the universal property,
                     stated before the proof
ATTACK     contracts/attacks/PDD-8/Attack.lean
           elaborated by hand:
           `lake env lean contracts/attacks/PDD-8/Attack.lean`
```

## STATUS — **STANDS-AMENDED. Six holes CLOSED; HOLE-2 open BY DESIGN.**

Re-run against the amended castle `d74e6ee0` and packet `de720d7b` on
2026-08-30. Six of the seven holes close with mechanical evidence;
HOLE-2 is recorded in the packet's break ledger as `FIXED-BY NOT FIXED
… RULING OWED`, with the `:263` discharge claim WITHDRAWN and
`EFFECTS-BACKEND.md` untouched — verified, not taken on report. The
re-run record is `AttackAmended.lean` beside this file; the closure
verdicts are the **Re-run** section at the end.

One correction against THIS file, kept rather than quietly fixed:
HOLE-3's sentence said three declarations "spend one equation". That is
right for L17 and `through_id_left` and WRONG for `through_assoc`, which
spends the left unit AND associativity. `through_assoc_holds_over_collapse`
proved `[LawfulMonad M]` was not NECESSARY; it never identified what
suffices. The fix pass states it at two equations, and the re-run proves
those two are MINIMAL — neither droppable — which the fix pass did not
show either.

`Attack.lean` is UNEDITED and stays the record against
`6ce34fff`/`8a241313`. It re-elaborates clean against `d74e6ee0`; that
is expected and is not itself evidence of closure — an amended law set
that EXTENDS the original cannot falsify a theorem about the original.

---

# VERDICT (first pass) — **STANDS-with-holes** (7 HOLEs, 6 NOTEs; no BREAK)

Every theorem in the castle reproduces. No law is false, nothing is
irreproducible, no axiom is smuggled, the commit order is packet-first,
the file frame holds and every byte gate is green. The three falsifiers
re-elaborate from apparatus re-declared outside the castle's file, so
none of them leans on anything private to it.

What does not hold is the castle's account of its own reach. Seven
claim-scope and adequacy gaps: the headline word "initial" is false in
the only category the file names; the citation that word is said to
discharge binds it to a different theorem; three declarations demand
more of their target than they spend, by the exact standard the castle
applied to L18; one falsifier's headline is refuted at its own
signature; the boundary theorem does not prove what its name says and
the reason given for the boundary is false; the adequacy pin is vacuous
over the castle's own unlawful monad and its anti-vacuity companion does
not cover it; and the boundary enumeration misses two semantics living
in this same repository.

---

## Gates and census

### `lake --wfail build`, from `library/cas`

```
✔ [46/95] Built Cas.Backend.Universal (1.5s)
Build completed successfully (95 jobs).
```

The job list carries `Cas.Backend.Universal`, and the gate is REAL, not
nominal — both halves of the castle's placement rationale were verified
empirically rather than taken on the castle's word:

- `theorem breaker_sorry_probe : False := by sorry` appended to
  `Cas/Backend/Universal.lean` turns `--wfail` RED:

  ```
  ⚠ [94/95] Building Cas.Backend.Universal (3.3s)
  warning: Cas/Backend/Universal.lean:453:8: declaration uses `sorry`
  Some required targets logged failures:
  - Cas.Backend.Universal
  error: build failed
  ```

- the same `sorry` planted in a NEW, unimported `Cas/Lang/BreakerProbe.lean`
  leaves `--wfail` GREEN (`Build completed successfully (95 jobs).`) and
  produces no job for it at all. The castle's claim that a new
  `Cas/Lang/*.lean` is silently unchecked is TRUE, and the `Cas.Backend.+`
  placement buys a real gate.

Both probes were reverted; `git status --short` is clean apart from this
attack directory.

### `mise run --force check:cas`

Green, end to end, with the castle and this attack directory both in the
tree:

```
ok vectors/index.json (2045 bytes) — 7 vectors
ok schemas/index.json (1031 bytes) — 10 schemas
ok conformance/schema-verdicts.json (71998 bytes) — 68 cases
ok conformance/admission-map.json (10414 bytes) — 22 rows (10 admitted, 10 deferred, 2 rejected)
ok ../effects/test/generated/VectorProgramAddresses.json (2816 bytes) — 7 program addresses
ok REGISTRY.md (14529 bytes) — 11 sorts, the kind-tag registry
ok ../../docs/lab-core/ENVIRONMENT.json (37002 bytes) — 45 tasks, 16 exes, 8 pins (2 distinct)
ok surface/cas-surface.json (955041 bytes) — 2026 declarations
10 of 10 controls fire
ok surface/cas-obligations.json (17363 bytes) — 68 obligations
13 of 13 controls fire
ok surface/cas-laws.json (9825 bytes) — 9 of 37 rulings bound, 28 unbound
[exited with code 0]
```

(Excerpted; every emitter's `--check` line is `ok`, and the two ledgers'
planted-defect controls all fire before the gates they vouch for. The
committed `surface/cas-surface.json` is byte-identical to what the
environment holding the castle emits, and neither lane commit touched
that file — which is the packet's "moves no byte" claim, confirmed.)

`Walk.libraryImports` (`tools/Walk.lean:45-55`) does not name
`Cas.Backend.Universal`, as the packet says. The attack directory sits
outside every `srcDir`, every `globs` and every `sources` entry of
`check:cas`, so it moves nothing either.

### Axiom census — mechanical, over the whole module

Not a hand-list: every constant whose defining module is
`Cas.Backend.Universal`, with `Lean.collectAxioms` on each. 34
declarations, 22 public, 12 private.

```
PUBLIC  theorem Cas.Lang.Handler.ext :: [Quot.sound]
PUBLIC  inductive Cas.Lang.IsMonadMorphism :: []
PUBLIC  theorem Cas.Lang.IsMonadMorphism.bind_law :: []
PUBLIC  ctor Cas.Lang.IsMonadMorphism.mk :: []
PUBLIC  theorem Cas.Lang.IsMonadMorphism.pure_law :: []
PUBLIC  theorem Cas.Lang.bind_law_is_load_bearing :: []
PUBLIC  theorem Cas.Lang.existsUnique_handler :: [Quot.sound, propext]
PUBLIC  theorem Cas.Lang.exists_handler_of_isMonadMorphism :: [Quot.sound, propext]
PUBLIC  theorem Cas.Lang.handler_eq_of_interpret_eq :: [Quot.sound, propext]
PUBLIC  theorem Cas.Lang.handler_eq_of_interpret_op_eq :: [Quot.sound, propext]
PUBLIC  theorem Cas.Lang.interpret_isMonadMorphism :: [Quot.sound, propext]
PUBLIC  theorem Cas.Lang.interpret_of_isMonadMorphism :: [Quot.sound, propext]
PUBLIC  theorem Cas.Lang.interpret_pinned :: [Quot.sound, propext]
PUBLIC  theorem Cas.Lang.interpret_satisfies_the_property :: [Quot.sound, propext]
PUBLIC  theorem Cas.Lang.interpret_vis :: []
PUBLIC  theorem Cas.Lang.run_fixed_fuel_is_not_compositional :: [propext]
PUBLIC  theorem Cas.Lang.single_type_agreement_is_not_enough :: []
PUBLIC  theorem Cas.Lang.through_assoc :: [Quot.sound, propext]
PUBLIC  theorem Cas.Lang.through_id_left :: [Quot.sound, propext]
PUBLIC  theorem Cas.Lang.through_id_right :: [Quot.sound]
PUBLIC  theorem Cas.Lang.through_monoid :: [Quot.sound, propext]
PUBLIC  theorem Cas.Lang.uniqueness_needs_lawful :: []
private def  ... Collapse, OneSig, St, hTrue, hFalse, hInc, hNop,
             loadOnce, phiDrifts, twoOps, instMonadCollapse :: []
private theorem ... collapse_interpret :: []
```

**The packet's census is exact.** Axiom union `{propext, Quot.sound}`;
no `sorryAx`, no `Classical.choice`, no `Lean.ofReduceBool`, no
declaration of kind `axiom`. And the count claim holds to the letter:
exactly FOUR theorems depend on no axiom at all — `interpret_vis`,
`uniqueness_needs_lawful`, `single_type_agreement_is_not_enough`,
`bind_law_is_load_bearing` — which are the four the packet names.

### Commit order

```
8f821ffa 2026-08-30 02:08:12  packet    contracts/PDD-8.contract.md   +473
6ce34fff 2026-08-30 02:10:51  castle    Cas/Backend/Universal.lean    +436
8a241313 2026-08-30 02:12:33  pin       Cas/Backend/Universal.lean     +15
```

Packet-first, by two minutes and by file. Two files touched across the
whole lane, both new; no existing file edited; no lakefile edit; no
merge-branch file. The ticket's fence holds.

### This attack's own census

```
bare_monad_strengthening_is_real            [propext]
shift_admits_no_morphism                    [propext, Quot.sound]
one_type_can_be_enough                      [propext, Quot.sound]
l17_holds_where_the_castle_cannot_state_it  [Quot.sound]
prog_is_not_initial_among_monads            [propext, Quot.sound]
prog_is_initial_in_S_models                 [propext, Quot.sound]
run_has_no_composition_law                  [propext, Quot.sound]
interpret_pinned_is_vacuous_over_collapse   [Quot.sound]
pinned_needs_op_agreement                   [propext, Quot.sound]
pinned_needs_the_morphism_law               (no axioms)
```

---

## Findings

### HOLE-1 — "`Prog S` is initial" is FALSE in the only category the file names

**Attacked:** `existsUnique_handler`'s docstring
(`Cas/Backend/Universal.lean:252-255`) and §5's prose (`:221`): "**`Prog S`
is initial**: every monad morphism out of it is induced by exactly ONE
handler"; "With L17 that is INITIALITY".

**Witness** (`Attack.lean` §4a, `prog_is_not_initial_among_monads`):

```lean
theorem prog_is_not_initial_among_monads :
    IsMonadMorphism OneSig (fun {_A} p => interpret hInc p)
      ∧ IsMonadMorphism OneSig (fun {_A} p => interpret hNop p)
      ∧ interpret hInc (Prog.op ()) ≠ interpret hNop (Prog.op ())
```

Two DISTINCT monad morphisms out of `Prog OneSig` into one lawful
target (`StateT Nat Id`), separated at state `0` by `((), 1)` against
`((), 0)`. An initial object admits exactly one morphism to each object.
`IsMonadMorphism` is the only morphism notion the file defines, so the
category the reader is handed is monads-and-monad-morphisms, and in that
category `Prog S` is not initial — not for one signature, not for any.

**What the theorem after the colon actually proves** is a HOM-SET
BIJECTION: `interpret` is a bijection `Handler S M ≃ Mor(Prog S, M)`.
That is FREENESS — the free-monad adjunction, and the right and useful
theorem. It is not initiality, and the gloss "is initial:" asserts one
and delivers the other.

**Repair, supplied and proved** (`Attack.lean` §4b,
`prog_is_initial_in_S_models`): the initiality that IS true lives in
the category of `S`-MODELS — objects `(M, h)`, morphisms the monad
morphisms respecting the chosen meanings — and `(Prog S, idHandler)` is
initial there:

```lean
theorem prog_is_initial_in_S_models (h : Handler S M) :
    ∃ φ : (A : Type) → Prog S A → M A,
      (IsMorphE S φ ∧ ∀ op, φ _ (Prog.op op) = h.handle op)
        ∧ ∀ ψ, IsMorphE S ψ → (∀ op, ψ _ (Prog.op op) = h.handle op) → ψ = φ
```

Note the quantifier order, which is the whole difference:
`existsUnique_handler` fixes a MORPHISM and produces a unique HANDLER;
initiality fixes a HANDLER and produces a unique MORPHISM. They are
inter-derivable, and only one of them is in the castle. Adding it is one
proof, already written above.

**Why HOLE and not BREAK:** every theorem in the castle is true. The
defect is that the word carrying the ruling ("INITIAL", R10's licence)
is attached to a statement that does not support it in the file's own
vocabulary.

### HOLE-2 — the pending word the packet discharges is bound, at the cited line, to a different theorem

**Attacked:** packet `LAW UP` note and `Cas/Backend/Universal.lean:253-255`
— "This is the theorem `EFFECTS-BACKEND.md:263`'s 'INITIAL' and
`Lang.lean:21`'s 'free monad' were naming… It is NOT
`eq_of_forall_interpret`."

**Witness** (documentary, `EFFECTS-BACKEND.md:262-265`, verbatim):

```
`LawfulMonad` (every normalizer rewrite licensed) and INITIAL
(`eq_of_forall_interpret`: agreement under every lawful interpretation
IS structural equality — no finer program equality exists); (3)
```

The cited line's own parenthetical binds INITIAL to
`eq_of_forall_interpret` — the declaration the packet says it is NOT.
So one of two things is true, and the packet asserts neither:

- R14 meant what it wrote, in which case UP is a DIFFERENT theorem and
  R14's word is not the one being discharged; or
- R14's word was a misuse, in which case the fix is to amend R14's text,
  which nothing in this lane does — the document still glosses INITIAL
  as `eq_of_forall_interpret` after `6ce34fff`.

For the record, `eq_of_forall_interpret` is not initiality either: it is
faithfulness of the syntactic semantics, `interpret_id` specialized at
`idHandler`. The estate now carries three distinct readings of one word
— faithfulness (R14), freeness (UP), and the initiality nobody stated
until §4b above. `Lang.lean:21`'s "free monad" is the one citation the
castle discharges cleanly, and it is discharged.

### HOLE-3 — three declarations demand more of their target than they spend, by the castle's own standard

**Attacked:** the packet's `REQUIRES` block ("`LawfulMonad M` for exactly
three: L13, L17 and `through_id_left` — and where it is required it is
LOAD-BEARING, which is falsifier F-LAWFUL, not a remark") against
`handler_eq_of_interpret_op_eq`, `handler_eq_of_interpret_eq`,
`through_id_left` and `through_assoc`.

F-LAWFUL establishes that dropping ALL of `LawfulMonad` breaks
uniqueness. It does not establish that `LawfulMonad` is what uniqueness
needs. It is not: L17's proof reaches `interpret_op`, and
`interpret_op`'s proof spends exactly ONE equation, `x >>= pure = x`.

**Witnesses** (`Attack.lean` §3c and §7 F3):

```lean
theorem uniqueness_from_right_unit [Monad M]
    (runit : ∀ {A} (x : M A), x >>= (fun a => pure a) = x)
    (e : ∀ op, interpret h (Prog.op op) = interpret g (Prog.op op)) : h = g

def RUnit (A : Type) : Type := Nat × A       -- pure a := (0, a)
instance : Monad RUnit where                 -- bind charges a surcharge
  bind x f := (if (f x.2).1 = 0 then x.1 else x.1 + (f x.2).1 + 1, (f x.2).2)

theorem runit_right_unit  (x : RUnit A) : x >>= (fun a => pure a) = x := rfl
theorem runit_not_lawful  : ¬ Nonempty (LawfulMonad RUnit)   -- pure_bind fails: 2 = 1
theorem l17_holds_where_the_castle_cannot_state_it           -- uniqueness, over RUnit
theorem through_id_left_over_runit                           -- the tower's left unit, over RUnit
```

Over `RUnit`, uniqueness and `through_id_left` are TRUE and the castle's
statements cannot even be typed — there is no `LawfulMonad RUnit`
instance to supply. And `through_assoc` holds over `Collapse`, the
castle's own unlawful monad:

```lean
theorem through_assoc_holds_over_collapse
    (t : Handler S (Prog T)) (u : Handler T (Prog U)) (h : Handler U Collapse) :
    (t.through u).through h = t.through (u.through h)
```

**Ground:** the castle's own NOTE L18 — "the review's §4 sketch declares
`[LawfulMonad M]` and does not use it… dropping it is a strictly stronger
theorem". Applied once, to the hypothesis the review left behind, and
not to the three the castle wrote itself.

**The named axiom, since the packet does not name one.**
`uniqueness_needs_lawful`'s witness violates `LawfulMonad.pure_bind`
(`collapse_not_lawful`: `pure () >>= (fun _ => false) = true`), and the
law L17 actually consumes is the right unit. The witness does not merely
"differ definitionally": it fails a stated axiom, proved.

### HOLE-4 — F-ONETYPE's headline is refuted at its own signature

**Attacked:** packet `F-ONETYPE` — "L17 read at ONE answer type proves
nothing" — and `single_type_agreement_is_not_enough`'s docstring, "This
is why `handler_eq_of_interpret_eq` quantifies over `A`".

**Witness** (`Attack.lean` §3d, `one_type_can_be_enough`):

```lean
theorem one_type_can_be_enough [Monad M] [LawfulMonad M]
    {h g : Handler OneSig M}
    (e : ∀ p : Prog OneSig Unit, interpret h p = interpret g p) : h = g
```

At `OneSig` — the signature the falsifier itself is built on — agreement
at the SINGLE answer type `Unit` forces handler equality outright,
because `Prog.op op : Prog OneSig Unit`. So "one answer type proves
nothing" is false; what is true, and what the theorem in the tree
proves, is that one BADLY CHOSEN answer type (`Empty`, uninhabited)
proves nothing. The theorem is right and the law line generalizes past
it. The honest law is "there is an answer type at which agreement is
vacuous", and the general-`S` motive for quantifying over `A` is that
answer types VARY WITH THE OPERATION — which the docstring's second
clause already says correctly, one sentence later.

### HOLE-5 — the boundary theorem does not prove non-compositionality, and the reason given for the boundary is false

Two defects, one section (`Cas/Backend/Universal.lean` §7(b), packet
`LAW BOUND`).

**5a — the stated reason.** §7(b) and the module docstring say `step`,
`run`, `stepRooted`, `runRooted` "are not maps `Prog S A → M A` at all".
That is false for `run` and for `step`. `Status CasSig` is a
`Type → Type`, so `fun A => Word → Status CasSig A × Word` is one, and
both families type-check against it — the definitions ARE the witness
(`Attack.lean` §5b):

```lean
def RunM (A : Type) : Type := Word → Status CasSig A × Word
instance : Monad RunM  where ...            -- so IsMonadMorphism is statable
def runAsMap  (fuel : Nat) : {A : Type} → Prog CasSig A → RunM A := fun p => run H fuel p
def stepAsMap             : {A : Type} → Prog CasSig A → RunM A := fun p => step H p
```

The continuation "escaping into the codomain" does not leave the shape:
it lands in `Status CasSig A`, indexed by the same `A`. The obstruction
is compositional, not shape-theoretic — and the difference is not
cosmetic. "Wrong shape" puts the operational semantics outside the
universal property forever; "no composition law at fixed fuel" is a fact
about a fuel discipline, and it is what the estate should be recording,
because `runP` (HOLE-7) is a fuel-free run that is still outside.

**5b — the missing theorem.** The packet's `FALS BOUND` demands
"show `run H f (p.bind g)` IS determined by `run H f p` and
`run H f ∘ g`". `run_fixed_fuel_is_not_compositional` does not answer
that: it computes one composite that outruns its parts, which is
evidence for the law, not the law. Determination is refuted by two
programs with the SAME run whose composites differ; the castle has one
program. Supplied (`Attack.lean` §5c):

```lean
theorem run3_load_once_eq_twice (a : Addr32) :
    (fun w => run H 3 (loadOnce a) w) = (fun w => run H 3 (loadTwice a) w)

theorem run_has_no_composition_law (a : Addr32) (n : Node) :
    ¬ ∃ comp, ∀ p f,
        (fun w => run H 3 (p.bind f) w)
          = comp (fun w => run H 3 p w) (fun u w => run H 3 (f u) w)
```

At fuel 3 one load and two loads are the same run AT EVERY WORD — both
halt `done` where the address binds, both refuse identically where it
does not — and binding a third load separates them (`done` against
`running (.pure ())`). That kills EVERY candidate composition law at
once, for any monad structure whatsoever, since any `bind` is in
particular a function of its two arguments. This is the statement the
name `run_fixed_fuel_is_not_compositional` promises.

The castle's own witness re-computes unchanged
(`re_run_fixed_fuel_is_not_compositional`): true, and weaker than its
name.

### HOLE-6 — the adequacy pin is vacuous over the castle's own unlawful monad, and commit `8a241313` does not reach it

**Attacked:** `interpret_pinned` (`[Monad M]`) against
`interpret_satisfies_the_property` (`[Monad M] [LawfulMonad M]`) — the
whole content of the "close the vacuity reading of the adequacy pin"
commit.

**Witness** (`Attack.lean` §7 F1):

```lean
theorem interpret_pinned_is_vacuous_over_collapse :
    ¬ ∃ I : Handler OneSig Collapse → {A : Type} → Prog OneSig A → Collapse A,
        (∀ h, IsMonadMorphism OneSig (fun {_A} p => I h p))
        ∧ (∀ h op, I h (Prog.op op) = h.handle op)
```

At `Collapse` — the target the castle's own F-LAWFUL falsifier uses —
`bind_law` at `(Prog.op op, Prog.pure)` forces `I h (Prog.op op) = true`,
and the operation-agreement hypothesis then demands
`hFalse.handle () = true`. The hypothesis class is EMPTY, so "there is
no wrong-but-passing interpreter" is true there only because there is no
interpreter there at all. The anti-vacuity companion carries
`[LawfulMonad M]` and vouches only for the lawful half of the pin's own
quantifier. Either the pin should be stated at `[LawfulMonad M]` — where
its companion actually reaches — or the companion should be strengthened
to say WHICH targets admit an `I`.

**And the pin's own hypotheses are never falsified**, though the packet
applies exactly that discipline to L17 and L18. Both drops fire
(`Attack.lean` §7 F2):

```lean
def IIgnores (_h : Handler OneSig St) := fun p => interpret hNop p
theorem pinned_needs_op_agreement :
    (∀ h, IsMonadMorphism OneSig (fun {_A} p => IIgnores h p))
      ∧ IIgnores hInc (Prog.op ()) ≠ interpret hInc (Prog.op ())

def IDrifts (h : Handler OneSig St) := fun p => phiDrifts hInc h p
theorem pinned_needs_the_morphism_law :
    (∀ h op, IDrifts h (Prog.op op) = h.handle op)
      ∧ IDrifts hNop twoOps ≠ interpret hNop twoOps
```

`IIgnores` is a morphism at every handler and ignores the handler;
`IDrifts` agrees with every handler on every single operation and is not
`interpret`. Both hypotheses of the pin are load-bearing, now on the
record.

### HOLE-7 — the boundary enumeration misses two semantics living in this repository

**Attacked:** the packet's claim-scope, "for each of the three semantics
the review found outside it, says exactly what the proof does and does
not reach", and §7 of the module. The enumeration is presented as THE
boundary and is nowhere declared non-exhaustive. Two more semantics are
in the tree, and neither of the packet's reasons reaches either.

**Fourth — `Cas.Lang.runP`** (`Cas/Lang/Defun.lean:293`), the direct
interpreter of the defunctionalized table:

```lean
def runPShape : (Bytes → Addr32) → PProg → Word → Status CasSig Addr32 × Word := runP
theorem runP_is_not_a_fuelled_run (p : PProg) (w : Word) :
    (runP H p w).1.isRunning = false := runP_halts H p w
```

Its domain is `PProg`, not `Prog S A`, so it is neither a handler nor a
map out of `Prog` — and the packet's reason for excluding the fueled
runs, "a fueled run reports `.running`", does NOT apply, because
`runP_halts` (already on main) proves it never does. It is a TOTAL
semantics of store programs outside the property's reach for a reason
the packet does not name. It is also the semantics the emitter's gate
actually executes.

**Fifth — `Cas.Lang.wp` / `Cas.Lang.wlp`** (`Cas/Lang/Wp.lean:150,154`),
the predicate-transformer semantics that PDD-2 landed in this same wave:

```lean
def wpShape  : (Bytes → Addr32) → PProg → WPost → WPre := wp
def wlpShape : (Bytes → Addr32) → PProg → WPost → WPre := wlp
```

Contravariant — postconditions to preconditions — so it is not of the
shape `Prog S A → M A` for any `M`, and no reading of R10's "a semantics
IS a handler" reaches it. The packet's claim-scope class explicitly
honours the WLP/WP distinction ("a WLP-shaped claim is not a termination
claim") and then does not place the estate's own WLP/WP transformer
against the property it is scoping.

**Why this matters and is not pedantry:** R10 is a RULING that a
semantics IS a handler. The packet's boundary is what tells a reader how
far that ruling reaches. An enumeration that reads as complete and is
not is exactly the claim-scope defect the class exists to catch. The
repair is one sentence — declare the enumeration to be the review's
three and not the estate's all — plus two rows.

---

## Notes

### NOTE-1 — L18's bare-`Monad` strengthening is real, and self-limiting

The ordered attack was: does `IsMonadMorphism` secretly encode
lawfulness, making the drop hollow? The answer is three-part, all
kernel-checked.

**It does encode lawfulness — on the image.** `bind_law` at
`p := Prog.pure a` gives the left unit; at `f := Prog.pure`, through
`Prog.bind_pure_right`, the right unit; twice, through
`Prog.bind_assoc'`, associativity — all restricted to values `φ p`, all
over an arbitrary `Monad M` (`Attack.lean` §2a: `image_left_unit`,
`image_right_unit`, `image_assoc`). A morphism out of `Prog S` drags the
monad laws onto its own image wherever it goes.

**It is NOT hollow.** `IsMonadMorphism` mentions `pure` and `>>=` and
nothing else; `LawfulMonad` also carries `LawfulApplicative` and
`LawfulFunctor`. `Ct` (`Attack.lean` §2b) is the counting monad with a
deliberately wrong `map`: impeccable `pure`/`bind`, `id_map` false, no
`LawfulMonad Ct` instance to be had. `interpret hTick` is a genuine,
NON-CONSTANT morphism into it, separating both programs and handlers:

```lean
theorem ct_not_lawful : ¬ Nonempty (LawfulMonad Ct)
theorem bare_monad_strengthening_is_real :
    IsMonadMorphism BoolSig (fun {_A} p => interpret hTick p)
      ∧ interpret hTick (Prog.op true) ≠ interpret hTick (Prog.op false)
      ∧ interpret hTick (Prog.op true) ≠ interpret hFlip (Prog.op true)
```

L18 applies there. A `[LawfulMonad M]`-bearing L18 does not. The
strengthening is cashed.

**Nor is it free.** `Shift` — the writer monad whose `pure` costs one —
admits NO morphism out of `Prog S` at all, because §2a's right unit
forces `n = n + 1`:

```lean
theorem shift_admits_no_morphism (φ : {A : Type} → Prog OneSig A → Shift A) :
    ¬ IsMonadMorphism OneSig φ
```

So "bare `Monad`" is a proper subclass on both sides, and the packet's
"strictly stronger theorem" is accurate but should not be read as "L18
now applies to arbitrary unlawful monads". None of this is written down
in the packet; it is the honest reading of the drop and it belongs
beside it.

### NOTE-2 — the negative byte gate proves less than the packet claims

The packet: "That is what makes the negative byte gate a real gate
rather than a formality."

Probe: `Cas/Backend/Universal.lean` was MOVED OUT OF THE TREE entirely
and `mise run --force check:cas` was re-run. It is fully green — every
byte-identity gate, every self-test, exit 0. The byte gate is a gate
against DRIFT in what is emitted; it says nothing about whether the
castle exists or what it proves, because the module is deliberately
outside `Walk.libraryImports` and outside every emitter's environment.

The only mechanism that binds the castle is `lake --wfail build`, which
does fire on a planted `sorry` (verified above) — and which is equally
green when the file is absent. Nothing in the estate's gate set would
notice this module's deletion. That is a property of the placement
device the packet chose, not a defect in the packet's honesty, and it is
the strongest argument for the promotion the packet defers: a theorem
nobody's ledger knows about is a theorem the estate cannot be said to
hold.

### NOTE-3 — the placement rationale is honest, and was verified both ways

The castle claims a new `Cas/Lang/*.lean` is silently unchecked and that
`Cas.Backend.+` buys a real gate. Both verified empirically, above.
`lakefile.toml`'s `CasBackend` glob is `Cas.Backend.+` and
`defaultTargets` carries it, so `Cas.Backend.Universal` is in the job
list at `[46/95]`.

### NOTE-4 — F-BIND asserts two premises in prose that are not in its theorem

The docstring says `phiDrifts` "respects `pure` and nothing else" and
that L18 "would read off the SAME handler". Neither is stated. Both are
true and both are one line, supplied (`Attack.lean` §3b):

```lean
theorem phiDrifts_pure_law (h g : Handler OneSig St) (a : A) :
    phiDrifts h g (Prog.pure a) = pure a := rfl
theorem phiDrifts_read_off :
    (⟨fun op => phiDrifts hInc hNop (Prog.op op)⟩ : Handler OneSig St) = hNop
```

Without the second, the disagreement at `twoOps` is a coincidence
rather than a refutation: the falsifier's force is that L18 reads the
SAME handler off both maps.

### NOTE-5 — the property's subject is a proper subclass of `Prog`

`Handler S M` fixes `M : Type → Type v`, so `interpret` exists only at
`A : Type`, while `Prog S A` is polymorphic in `A : Type u`. So there
are programs no handler can interpret — not "not yet", but not at the
shipped `Handler`:

```lean
def bigProg : Prog OneSig Type := .pure Nat
```

The packet discloses "every statement is at `A : Type`" under
claim-scope, which is accurate. The consequence it does not draw is that
R10's "a semantics IS a handler" is not merely unproved for such
programs — they have NO handler semantics at all.

### NOTE-6 — no name collision blocks the promotion

`Handler.ext`, `interpret_vis` and `IsMonadMorphism` are declared inside
`namespace Cas.Lang`, the library's own namespace, and none of the three
already exists there (`Cas/Lang/Auth.lean:387`'s `interpret_vis_state`
is a distinct name). Promoting the module into `Cas/Lang/` and into
`Walk.libraryImports` is not blocked by names; it would move the surface,
obligation and law ledgers, which is the ruling the packet correctly
defers.

---

## Failed attempts — recorded

A failed break is earned confidence, and earned confidence is record.

1. **Break the falsifier triad by re-elaboration.** All three castle
   falsifiers were re-proved from apparatus RE-DECLARED in the attack's
   own namespace (`OneSig`, `Collapse`, `hTrue`, `hFalse`, `St`, `hInc`,
   `hNop`, `phiDrifts`, `twoOps`), since the castle's are `private`.
   FAILED — `re_uniqueness_needs_lawful`,
   `re_single_type_agreement_is_not_enough`,
   `re_bind_law_is_load_bearing` all reproduce verbatim. None of them
   leans on anything private to the castle's file.

2. **Break L18's bare-`Monad` claim as a hollow strengthening.** FAILED.
   The image-law route (NOTE-1) shows the hypothesis is self-lawfulizing,
   which is the strongest form of the charge, and then `Ct` shows the
   drop still buys a non-empty, non-degenerate class of targets. The
   castle's sentence survives; what it does not survive is being read as
   "L18 now applies to any monad" (`shift_admits_no_morphism`).

3. **Break `interpret_pinned` with a wrong-but-passing interpreter over
   a lawful target.** FAILED, and provably: any `I` satisfying the
   morphism hypothesis equals `interpret` of its own read-off handler
   (L18), and the operation-agreement hypothesis forces that read-off
   handler to be `h` (L16). The search space is empty by construction.
   The adequacy discharge is genuine wherever the class is inhabited —
   which is the qualification HOLE-6 records.

4. **Break `through_assoc` / `through_monoid` / `through_id_right`.**
   FAILED. `through_id_right` has no hypotheses to attack (its target is
   `Prog T`); the monoid's carrier `Handler S (Prog S)` has a lawful `M`
   by construction; associativity survives every target tried, including
   the unlawful `Collapse`. The attempt did produce HOLE-3's third row —
   `through_assoc` holds where it cannot be stated.

5. **Break the axiom census.** FAILED. The mechanical walk over every
   constant in the module matches the packet's advance claim exactly,
   including the count of four axiom-free declarations and their names.

6. **Break the file frame and the byte gate.** FAILED.
   `Walk.libraryImports` does not name the module; `check:cas` is green
   with the castle and this attack directory both present; only two
   files were ever touched by the lane and both are new. The attempt
   produced NOTE-2 instead: the gate is green for the wrong reason as
   well as the right one.

7. **Break `Handler.ext`.** FAILED. `Handler` is a one-field structure;
   the theorem is `congrArg` after `funext` and there is nothing to
   exhibit against it.

---

## Break ledger rows owed to `contracts/PDD-8.contract.md`

The packet's `## Breaks` section is empty and says the breaker's pass
fills it or leaves it empty on the record. No BREAK row is owed — no law
is false. Seven claim-scope/adequacy rows are owed if the estate records
holes in that ledger; they are HOLE-1 through HOLE-7 above, each with
its witness declaration in `Attack.lean` and its close condition:

```
HOLE-1  close: replace "Prog S is initial" with "Prog S is FREE on S",
        and land `prog_is_initial_in_S_models` (proof supplied) if the
        word "initial" is to be kept in the estate.
HOLE-2  close: amend EFFECTS-BACKEND.md:263 — the word and its
        parenthetical disagree with the packet's reading of them.
HOLE-3  close: state L17, `through_id_left` and `through_assoc` at the
        hypothesis their proofs spend, or record why the surplus is
        deliberate.
HOLE-4  close: restate F-ONETYPE as "there is an answer type at which
        agreement is vacuous" — the theorem already proves that.
HOLE-5  close: land `run_has_no_composition_law` (proof supplied) and
        strike "not maps Prog S A → M A at all" from §7(b).
HOLE-6  close: state `interpret_pinned` at [LawfulMonad M], or extend
        `interpret_satisfies_the_property` to say which targets admit
        an I; and land the two hypothesis falsifiers (supplied).
HOLE-7  close: declare the boundary enumeration to be the review's
        three, and add `runP` and `wp`/`wlp` as rows.
```

---

# Re-run — against `d74e6ee0` (2026-08-30)

```
SUBJECT    d74e6ee0  PDD-8: the fix pass — six holes closed
PACKET     de720d7b  PDD-8: packet amendments — seven ledger rows
RECORD     contracts/attacks/PDD-8/AttackAmended.lean
           `lake env lean contracts/attacks/PDD-8/AttackAmended.lean`
FIRST PASS 6e6fa80a  (Attack.lean, unedited, still the record against
                     6ce34fff/8a241313)
```

## VERDICT — **STANDS-AMENDED**

Six holes closed. HOLE-2 open by design and correctly recorded. No new
BREAK, no new HOLE. One NOTE on the aliases, one on the census
arithmetic.

## Gates and census, re-measured

`lake --wfail build`: `✔ [94/95] Built Cas.Backend.Universal (8.6s)` /
`Build completed successfully (95 jobs).`

`mise run --force check:cas`: green end to end, `13 of 13 controls fire`,
`ok surface/cas-laws.json (9825 bytes)`. The module still moves no byte,
and `AttackAmended.lean` sits outside every target and every `sources`
glob, as `Attack.lean` does.

Axiom census, mechanical, over every constant whose defining module is
`Cas.Backend.Universal`:

```
                              packet de720d7b     breaker re-run
public constants                       78                 80
  of which theorems                    52                 52   ✓
axiom-free theorems                    22                 22   ✓
axiom sets  []                         44                 46
            [Quot.sound]               10                 10   ✓
            [propext]                   6                  6   ✓
            [propext, Quot.sound]      18                 18   ✓
union                    {propext, Quot.sound}  {propext, Quot.sound} ✓
```

No `sorryAx`, no `Classical.choice`, no `Lean.ofReduceBool`, no
declaration of kind `axiom`. **Every load-bearing figure reproduces.**
The two-constant gap is a counting convention and nothing else: my walk
counts `IsMonadMorphism.mk._flat_ctor` and `IsMorphE.mk._flat_ctor`, two
compiler artifacts of the two new structures, both axiom-free, both in
the `[]` bucket — which is exactly where the difference sits (46 v 44).
Filtering leading-underscore components gives 78. **NOTE-7 (minor):** the
packet's "78 public constants … recursors and projections included" is
not reproducible as stated without naming the filter; the number is
convention-dependent, and the packet should say which convention, since
it is a figure a later pass will be checked against.

## Closure verdicts, hole by hole

### HOLE-1 — **CLOSED**

`prog_is_free` carries the hom-set bijection under the correct word, and
`prog_is_initial_in_S_models` lands the initiality that was missing. Both
checked for statement FIDELITY rather than taken on the rename, because a
"generalization" that quietly drops a conclusion closes nothing
(`AttackAmended.lean` §1):

```lean
theorem breaker_4b_recovered [Monad M] [LawfulMonad M] (h : Handler S M) :
    ∃ φ : (A : Type) → Prog S A → M A, … :=
  prog_is_initial_in_S_models leftUnit_of_lawful bindAssoc_of_lawful
    rightUnit_of_lawful h

theorem prog_is_free_recovered [Monad M] [LawfulMonad M] (φ) (hφ) :
    ∃ h : Handler S M, … := prog_is_free rightUnit_of_lawful φ hφ
```

Both elaborate: the breaker's §4b statement is recovered verbatim at its
original hypotheses, and the freeness conclusion is unchanged. The
counter-witness that forced the hole is still true against the amended
castle (`still_not_initial_among_monads`, §5) — as it must be; a fix that
falsified it would have broken something. The castle's §6b docstring now
says so itself.

### HOLE-2 — **OPEN, BY DESIGN. Correctly recorded.**

Verified as asked, not accepted on report:

- the packet's break ledger row reads
  `FIXED-BY   NOT FIXED, and not this lane's to fix. … The claim to
  discharge :263 is WITHDRAWN in claim-scope; EFFECTS-BACKEND.md is
  untouched. RULING OWED.`
- claim-scope carries the three readings (faithfulness / freeness /
  initiality) with the declaration each binds to, and states that binding
  the word is an OPERATOR RULING;
- `git diff --name-only 8a241313 d74e6ee0` is exactly
  `Cas/Backend/Universal.lean` and `contracts/PDD-8.contract.md` —
  `EFFECTS-BACKEND.md` was not edited, so the word at `:263` still binds
  to `eq_of_forall_interpret` and the ruling is genuinely owed rather
  than pre-empted;
- the castle no longer claims to discharge it: no occurrence of
  "`Prog S` is initial" survives, and every "initial" in the file is
  either the S-models statement or the explicit denial of the monads
  reading.

Not silently dropped. This is the right disposition.

### HOLE-3 — **CLOSED, and pushed one step past where the fix pass stopped**

`LeftUnit`/`RightUnit`/`BindAssoc` are named, the bridges from
`LawfulMonad` are stated, and each theorem carries what it spends.

**The bridge spot-check, done adversarially.** The bridges would be
worthless if the three equations TOGETHER were equivalent to
`LawfulMonad` — the amendment would then be a re-spelling. The castle
exhibits `RUnit` (right unit only) and `Ct` (left unit + associativity)
separately; neither shows the BUNDLE is proper. It is
(`AttackAmended.lean` §2):

```lean
theorem ct_rightUnit : RightUnit Ct := fun _x => Prod.ext rfl (Nat.add_zero _)
theorem three_equations_do_not_imply_lawful :
    LeftUnit Ct ∧ RightUnit Ct ∧ BindAssoc Ct ∧ ¬ Nonempty (LawfulMonad Ct)
```

`Ct` satisfies all three equations and has no `LawfulMonad` instance, so
every restated theorem reaches at least one target the old statement
could not be applied to at all. The weakening is strictly proper as a
bundle, not merely per-equation.

**The `through_assoc` correction — accepted; the first pass was wrong.**
HOLE-3's sentence generalized "one equation" across three declarations.
`through_assoc` runs through `interpret_bind` and spends the left unit
AND associativity. `through_assoc_holds_over_collapse` proved only that
`[LawfulMonad M]` is not NECESSARY — in `Collapse` every interpretation
is `true`, so the conclusion holds for a reason outside any equation. It
never identified what suffices. `through_assoc_over_ct` is the right
witness and the castle has it.

**And the two equations are MINIMAL — which the fix pass did not show.**
A hypothesis set is minimal when no proper subset suffices, so two
counter-targets are owed. Both constructed (`AttackAmended.lean` §3):

```lean
-- Shift: pure costs ONE. Associativity holds; the left unit never does.
theorem shift_bindAssoc      : BindAssoc Shift
theorem shift_not_leftUnit   : ¬ LeftUnit Shift
theorem through_assoc_fails_over_shift :
    (tPass.through tPass).through hShift ≠ tPass.through (tPass.through hShift)
    -- one operation, one service: 2 against 3

-- Skew: both units hold; two non-zero costs combine non-associatively.
theorem skew_leftUnit        : LeftUnit Skew
theorem skew_rightUnit       : RightUnit Skew
theorem skew_not_bindAssoc   : ¬ BindAssoc Skew
theorem through_assoc_fails_over_skew :
    (tTwice.through tTwice).through hSkew ≠ tTwice.through (tTwice.through hSkew)
    -- four operations: 15 against 9

theorem through_assoc_two_equations_are_minimal :   -- the pair, packaged
```

`{BindAssoc}` alone is insufficient and `{LeftUnit, RightUnit}` is
insufficient: neither `lu` nor `ba` can be dropped, so the castle's
two-equation statement is exactly right. Without these the two-equation
form would be the same surplus HOLE-3 objected to, one equation smaller.

The one-equation statements need no minimality witness: drop the only
hypothesis and `uniqueness_needs_lawful` — the castle's own falsifier —
is the counter-target.

### HOLE-4 — **CLOSED**

`single_type_agreement_is_not_enough`'s docstring is restated as "a
BADLY CHOSEN answer type" and says outright that the first draft's
headline was false; `one_type_can_be_enough` is landed beside it as the
counter-witness that forced the amendment, at `RightUnit` rather than
`[LawfulMonad M]`. The general-`S` motive (answer types vary with the
operation) is now stated separately from the vacuity witness, which is
the distinction the hole was about.

### HOLE-5 — **CLOSED, both halves**

`run_has_no_composition_law` is landed as THE boundary theorem, adopted
with its proof and its `run3_load_once_eq_twice` lemma. The old theorem
is renamed `run_composite_outruns_its_parts` — "the old name promised the
law and delivered the witness" — and kept as the witness it always was.
The false reason is gone: §8 no longer says the operational semantics are
"not maps `Prog S A → M A` at all", and `RunM`, `runAsMap`, `stepAsMap`
and the `Monad RunM` instance are in the castle, so the shape refutation
is now the castle's own.

### HOLE-6 — **CLOSED**

`interpret_inhabits_the_pin` is restated at the three equations, so it
covers the pin's actual `[Monad M]` quantifier far more widely than the
`[LawfulMonad M]` companion did. Cashed rather than asserted
(`AttackAmended.lean` §2):

```lean
theorem pin_inhabited_at_ct :
    (∀ h : Handler OneSig Ct, IsMonadMorphism OneSig …)
      ∧ ∀ h op, interpret h (Prog.op op) = h.handle op :=
  interpret_inhabits_the_pin ct_leftUnit ct_bindAssoc ct_rightUnit
```

`Ct` has no `LawfulMonad` instance, so the first draft's companion could
not be instantiated there at all; the amended one can.

**F-PIN-EMPTY is LIVE in the castle**, not merely in the attack record:
`interpret_pinned_is_vacuous_over_collapse` is `Universal.lean:640`, and
`interpret_pinned`'s own docstring carries the scope ("a statement about
a class that is EMPTY at some targets"). Both hypothesis falsifiers
(`pinned_needs_op_agreement`, `pinned_needs_the_morphism_law`) are in the
castle too.

### HOLE-7 — **CLOSED**

§8 opens with "**The enumeration is the REVIEW's three, not the estate's
all**" and adds `runP` and `wp`/`wlp` as rows, with the shapes
type-checking against the shipped declarations (`runPShape`,
`runP_never_running`, `wpShape`, `wlpShape`). It also declines to claim
the new list is complete — "it is the semantics this lane could find" —
which is the correct disposition for an enumeration nobody has proved
exhaustive.

## Fresh probe — alias fidelity

The fix pass kept `existsUnique_handler` and
`interpret_satisfies_the_property` as aliases "so … any reader who
followed the old prose still resolve". Probed, because an alias that
changed its conclusion would be the worst kind of silent regression
(`AttackAmended.lean` §4):

```lean
theorem existsUnique_handler_old_call [Monad M] [LawfulMonad M] (φ) (hφ) :
    ∃ h : Handler S M, … := existsUnique_handler rightUnit_of_lawful φ hφ
theorem interpret_satisfies_the_property_old_call [Monad M] [LawfulMonad M] : … :=
    interpret_satisfies_the_property leftUnit_of_lawful bindAssoc_of_lawful
      rightUnit_of_lawful
theorem aliases_are_the_theorems_they_alias … :
    existsUnique_handler runit φ hφ = prog_is_free runit φ hφ := rfl
```

Both old signatures are recoverable and each alias is definitionally the
theorem it aliases. **NOTE-8 (minor):** the aliases preserve the NAME and
the CONCLUSION, not the CALL — `[LawfulMonad M]` became an explicit
equation argument, so an old application does not re-typecheck without a
bridge. Harmless here: a sweep of `library/`, `docs/` and `.staging/` for
`existsUnique_handler`, `interpret_satisfies_the_property`, `prog_is_free`
and `prog_is_initial` finds references ONLY in
`contracts/PDD-8.contract.md`, all consistent with the amended names, and
nothing imports the module. The packet's "still resolve" should read
"still resolves by name".

**Stale-prose sweep:** no occurrence of the freeness theorem described as
initiality survives anywhere in the castle or the packet. The one
remaining "INITIAL" bound to a different theorem is
`EFFECTS-BACKEND.md:263`, untouched on purpose — HOLE-2, ruling owed.

## Re-run failed attempts

1. **Break the two adopted theorems by statement drift** — check whether
   `prog_is_free` / `prog_is_initial_in_S_models` lost anything in the
   restatement to equations. FAILED: both original statements recover by
   instantiation.
2. **Break the `*_of_lawful` bridges as circular or vacuous.** FAILED:
   they are one-directional, and `Ct` proves the three-equation bundle is
   strictly weaker than `LawfulMonad`.
3. **Break the aliases.** FAILED: definitionally the theorems they alias;
   old signatures recoverable. Produced NOTE-8 only.
4. **Break `through_assoc`'s two-equation statement as still-surplus** —
   look for a one-equation proof. FAILED, decisively: the two equations
   are minimal, and the attempt turned into the minimality proof above.
5. **Break the census.** FAILED on every load-bearing figure; produced
   NOTE-7, a counting convention.
6. **Break HOLE-2's disposition** — check whether the withdrawal was
   cosmetic and `EFFECTS-BACKEND.md` quietly amended anyway. FAILED: the
   file is untouched and the ledger row says `RULING OWED`.

## Disposition

Six holes closed with mechanical evidence, each against the breaker's own
supplied statement rather than a paraphrase of it. HOLE-2 is open, and it
is open in the right way: the overclaim withdrawn, the cited document
left alone, the ruling named and owed. **PDD-8 lands, with the INITIAL
word binding flagged as an operator ruling.**
