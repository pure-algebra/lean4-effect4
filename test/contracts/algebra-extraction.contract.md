# Algebra extraction contract packet

Status: FROZEN / RED, breaker-authored 2026-08-31

Implementation fence: `Effect4/Algebra/**`

Battery: `Effect4Test/Algebra/ExtractionContract.lean`

Counterexamples: `test/counterexamples/REGISTER.md`, rows `E4-ALG-CE-001`
through `E4-ALG-CE-007`

## Degree and claim boundary

I have shown algebraically that this slice can be implemented to the degree of:

- kernel-checked constructor, monad, interpretation, sum, universal-property,
  and handler-composition equations;
- an explicit universe policy that prevents construction of a program which
  its handler kind cannot interpret;
- exact source-span and byte-digest provenance for every Foldlab declaration
  being extracted; and
- executable Lean falsifiers for the public surface and representative
  mutations.

This packet does not claim that the higher-order `Program` proof carrier is
serializable, that a bounded runner is compositional, or that TypeScript host
code has been preserved. Those are separate first-order-flow and conformance
obligations.

Obligation classes: **domain, contract, adequacy, termination, abstraction,
conformance, claim-scope**. There is no mutable-state frame inside the algebra;
the repository frame below still applies.

## Frozen Foldlab source

Foldlab commit: `feb29321fd50204aa338209d313e84a3f8b71c66`

The paths below are evidence inputs only. Effect4 must not import Foldlab.

| Source | Exact retained span | Effect4 disposition | SHA-256 of whole source file |
| --- | ---: | --- | --- |
| `library/cas/Cas/Lang/Sig.lean` | 1–27 | `Effect4/Algebra/Signature.lean`; generic declaration and sum | `91e9d984fead2a36c4503bb8db979e8f085123db754a655846888aac41e87cd6` |
| `library/cas/Cas/Lang/Prog.lean` | 1–54 | `Effect4/Algebra/Program.lean`; finite higher-order proof carrier | `a8ac15632d155f9558db1969f2a25faf548e337c35b584f54316d5aba0f958aa` |
| `library/cas/Cas/Lang/Handler.lean` | 39–67 | `Effect4/Algebra/Handler.lean`; handler, interpretation, bind law, sum | `7170bd9c6de8743d10fff712644fa1d6ce59100e5dc33e0458b17897de933bf9` |
| `library/cas/Cas/Lang/Representation.lean` | 35–118 | `Effect4/Algebra/Laws.lean`; lawful monad, identity interpretation, operation equations | `5ca0f4cfeeb396c0f084d547a72825ddbe8a6c6a37e0786dbed9e94d68b652a8` |
| `library/cas/Cas/Lang/Representation.lean` | 119–128 | deferred to `Effect4/Semantics/Equivalence.lean`; not part of this implementation fence | `5ca0f4cfeeb396c0f084d547a72825ddbe8a6c6a37e0786dbed9e94d68b652a8` |
| `library/cas/Cas/Lang/Tower.lean` | 63–85 | `Effect4/Algebra/Handler/Composition.lean`; `through` and collapse | `02b348347431dd80544427bb93fd0c0878b37ac010196ee1faf0c5925773027a` |
| `library/cas/Cas/Backend/SumAlgebra.lean` | 172–173, 196–467 | `Effect4/Algebra/Sum.lean`; operation bind, sum projections, injections, uniqueness | `d6a67f6efa75d81662f79945ce84ce54e83392b786bd9ce5a4884c01c2f7070b` |
| `library/cas/Cas/Backend/Universal.lean` | 127–223 | `Effect4/Algebra/MonadLaws.lean`; exact equations consumed by proofs | `cce4f2a50a7e2a2e8b57b4de1a82f90c86efcb9749683795fd2b9e96d2ad8010` |
| `library/cas/Cas/Backend/Universal.lean` | 294–349, 469–625 | `Effect4/Algebra/Universal.lean`; morphisms, freeness, initiality in models, pin | `cce4f2a50a7e2a2e8b57b4de1a82f90c86efcb9749683795fd2b9e96d2ad8010` |
| `library/cas/Cas/Backend/Universal.lean` | 739–749, 757–768, 785–790 | `Effect4/Algebra/Handler/Category.lean`; category laws and endomorphism monoid | `cce4f2a50a7e2a2e8b57b4de1a82f90c86efcb9749683795fd2b9e96d2ad8010` |

The original generic tests are the PDD-7/PDD-8 contracts and attacks, the
generic adversaries in `SumAlgebra.lean:643–1022`, and the `Ct`, `RUnit`,
`Collapse`, drifting-interpreter, missing-operation-agreement, and minimal
tower witnesses in `Universal.lean`. CAS-specific failures, `RefM`, and byte
observations are deliberately excluded from this slice.

## CATEGORIES

Assigned and added by the breaker:

- `contracts` — CATALOG §1.4: an exported theorem must state everything a
  client may rely on;
- `wp-sp-calculus` — §2.6: interpretation of sequencing preserves order;
- `inductive-data` — §4.2: `pure` and `vis` constructor equations are the
  proof carrier's defining equations;
- `lemmas-proofs` — §5.2: no bodyless law or circular proof counts;
- `algebraic-laws` — §§6.2 and 7.2: units, associativity, homomorphism, and
  reconstruction;
- `specification-design` — §8.0: the conjunction of laws, not one favorable
  equation, is the meaning;
- `abstraction-modules` — §§9.2, 9.3, and 9.5: the export is closed and every
  operation commutes with interpretation;
- `proof-mechanics` — §B.7: every program, operation, handler, and target in
  the stated range is quantified, not sampled.

## Existing-type disposition

There is exactly one generic signature, program, and handler family in
Effect4. The new library owns them. A later Foldlab adapter may alias them or
define conversions with two round-trip theorems; it may not make a second
generic semantic carrier. Foldlab keeps CAS operations, answer definitions,
refusals, words, reference handlers, and canonical bytes until their own
closure rows are complete.

`Program` remains the finite higher-order proof carrier: its continuation is a
Lean function from the operation's answer. First-order graph/program content
is a separate later type with an explicit embedding. No `Serialize`,
`DecidableEq`, hash identity, or raw `Lean.Expr` field belongs on `Program`.

## Public declaration signature proposal

Names below are frozen for the builder. Binder names may differ; universes,
argument roles, result types, and theorem propositions may not. The public
surface lives in namespace `Effect4`.

```lean
universe uOp uAns uS uT uU u v

structure Signature where
  Op : Type uOp
  Answer : Op → Type uAns

def Signature.sum
    (S : Signature.{uS, uAns}) (T : Signature.{uT, uAns}) :
    Signature.{max uS uT, uAns}

inductive Program (S : Signature.{uOp, uAns}) (A : Type uAns) where
  | pure (value : A)
  | vis (operation : S.Op)
      (next : S.Answer operation → Program S A)

variable {S : Signature.{uS, uAns}}
variable {T : Signature.{uT, uAns}}
variable {U : Signature.{uU, uAns}}
variable {A B C : Type uAns}
variable {M : Type uAns → Type v}

def Program.bind : Program S A → (A → Program S B) → Program S B
instance : Monad (Program S)
instance : LawfulMonad (Program S)

def Program.perform (operation : S.Op) : Program S (S.Answer operation)
def Program.inl : Program S A → Program (S.sum T) A
def Program.inr : Program T A → Program (S.sum T) A

structure Handler (S : Signature.{uOp, uAns})
    (M : Type uAns → Type v) where
  handle : (operation : S.Op) → M (S.Answer operation)

-- `Handler.ext` is the structure's generated extensionality theorem.
def interpret [Monad M] (handler : Handler S M) : Program S A → M A
def Handler.sum (left : Handler S M) (right : Handler T M) :
  Handler (S.sum T) M

abbrev LeftUnit (M : Type u → Type v) [Monad M] : Prop :=
  ∀ {A B : Type u} (a : A) (f : A → M B),
    (pure a : M A) >>= f = f a

abbrev RightUnit (M : Type u → Type v) [Monad M] : Prop :=
  ∀ {A : Type u} (value : M A),
    value >>= (fun a => (pure a : M A)) = value

abbrev BindAssoc (M : Type u → Type v) [Monad M] : Prop :=
  ∀ {A B C : Type u} (value : M A) (f : A → M B) (g : B → M C),
    (value >>= f) >>= g = value >>= fun a => f a >>= g

theorem Program.bind_pure_right (program : Program S A) :
  program.bind Program.pure = program

theorem Program.bind_assoc (program : Program S A)
    (f : A → Program S B) (g : B → Program S C) :
  (program.bind f).bind g = program.bind fun a => (f a).bind g

theorem Program.perform_bind (operation : S.Op)
    (next : S.Answer operation → Program S B) :
  (Program.perform operation).bind next = Program.vis operation next

theorem interpret_pure [Monad M] (handler : Handler S M) (value : A) :
  interpret handler (Program.pure value) = pure value

theorem interpret_perform [Monad M] [LawfulMonad M]
    (handler : Handler S M) (operation : S.Op) :
  interpret handler (Program.perform operation) = handler.handle operation

theorem interpret_bind [Monad M] [LawfulMonad M]
    (handler : Handler S M) (program : Program S A)
    (next : A → Program S B) :
  interpret handler (program.bind next) =
    interpret handler program >>= fun a => interpret handler (next a)

theorem interpret_bind_of_equations [Monad M]
    (leftUnit : LeftUnit M) (assoc : BindAssoc M)
    (handler : Handler S M) (program : Program S A)
    (next : A → Program S B) :
  interpret handler (program.bind next) =
    interpret handler program >>= fun a => interpret handler (next a)

def identityHandler : Handler S (Program S)
theorem interpret_identity (program : Program S A) :
  interpret identityHandler program = program

theorem Handler.sum_handle_inl (left : Handler S M) (right : Handler T M)
    (operation : S.Op) :
  (left.sum right).handle (.inl operation) = left.handle operation

theorem Handler.sum_handle_inr (left : Handler S M) (right : Handler T M)
    (operation : T.Op) :
  (left.sum right).handle (.inr operation) = right.handle operation

theorem Handler.sum_unique (left : Handler S M) (right : Handler T M)
    (candidate : Handler (S.sum T) M)
    (onLeft : ∀ operation,
      candidate.handle (.inl operation) = left.handle operation)
    (onRight : ∀ operation,
      candidate.handle (.inr operation) = right.handle operation) :
  candidate = left.sum right

theorem interpret_inl [Monad M] (left : Handler S M) (right : Handler T M)
    (program : Program S A) :
  interpret (left.sum right) (Program.inl program) = interpret left program

theorem interpret_inr [Monad M] (left : Handler S M) (right : Handler T M)
    (program : Program T A) :
  interpret (left.sum right) (Program.inr program) = interpret right program

theorem Program.inl_pure (value : A) :
  Program.inl (T := T) (Program.pure value : Program S A) = Program.pure value

theorem Program.inr_pure (value : A) :
  Program.inr (S := S) (Program.pure value : Program T A) = Program.pure value

theorem Program.inl_bind (program : Program S A) (next : A → Program S B) :
  Program.inl (T := T) (program.bind next) =
    (Program.inl (T := T) program).bind
      (fun a => Program.inl (T := T) (next a))

theorem Program.inr_bind (program : Program T A) (next : A → Program T B) :
  Program.inr (S := S) (program.bind next) =
    (Program.inr (S := S) program).bind
      (fun a => Program.inr (S := S) (next a))

theorem Program.inl_injective :
  Function.Injective (Program.inl (S := S) (T := T) (A := A))

theorem Program.inr_injective :
  Function.Injective (Program.inr (S := S) (T := T) (A := A))

def leftInjectionHandler : Handler S (Program (S.sum T))
def rightInjectionHandler : Handler T (Program (S.sum T))

theorem Program.inl_unique
    (candidate : {A : Type uAns} → Program S A → Program (S.sum T) A)
    (square : ∀ {A : Type uAns} (program : Program S A),
      interpret (leftInjectionHandler.sum rightInjectionHandler)
          (candidate program) =
        interpret leftInjectionHandler program)
    (program : Program S A) : candidate program = Program.inl program

theorem Program.inr_unique
    (candidate : {A : Type uAns} → Program T A → Program (S.sum T) A)
    (square : ∀ {A : Type uAns} (program : Program T A),
      interpret (leftInjectionHandler.sum rightInjectionHandler)
          (candidate program) =
        interpret rightInjectionHandler program)
    (program : Program T A) : candidate program = Program.inr program

structure IsMonadMorphism (S : Signature.{uOp, uAns})
    {M : Type uAns → Type v} [Monad M]
    (map : {A : Type uAns} → Program S A → M A) : Prop where
  pure_law : ∀ {A} (a : A), map (Program.pure a) = pure a
  bind_law : ∀ {A B} (p : Program S A) (f : A → Program S B),
    map (p.bind f) = map p >>= fun a => map (f a)

theorem interpret_isMonadMorphism [Monad M] [LawfulMonad M]
    (handler : Handler S M) :
  IsMonadMorphism S (fun {_A} program => interpret handler program)

theorem interpret_of_isMonadMorphism [Monad M]
    (map : {A : Type uAns} → Program S A → M A)
    (laws : IsMonadMorphism S map) (program : Program S A) :
  map program =
    interpret (M := M) ⟨fun operation => map (Program.perform operation)⟩ program

theorem exists_handler_of_isMonadMorphism [Monad M]
    (map : {A : Type uAns} → Program S A → M A)
    (laws : IsMonadMorphism S map) :
  ∃ handler : Handler S M,
    ∀ {A : Type uAns} (program : Program S A),
      map program = interpret handler program

theorem handler_eq_of_interpret_operation_eq [Monad M]
    (rightUnit : RightUnit M) {left right : Handler S M}
    (equal : ∀ operation : S.Op,
      interpret left (Program.perform operation) =
        interpret right (Program.perform operation)) :
  left = right

theorem handler_eq_of_interpret_eq [Monad M]
    (rightUnit : RightUnit M) {left right : Handler S M}
    (equal : ∀ {A : Type uAns} (program : Program S A),
      interpret left program = interpret right program) :
  left = right

theorem program_is_free [Monad M]
    (rightUnit : RightUnit M)
    (map : {A : Type uAns} → Program S A → M A)
    (laws : IsMonadMorphism S map) :
  ∃ handler : Handler S M,
    (∀ {A : Type uAns} (program : Program S A),
      map program = interpret handler program) ∧
    ∀ other : Handler S M,
      (∀ {A : Type uAns} (program : Program S A),
        map program = interpret other program) →
      other = handler

theorem program_is_initial_in_models [Monad M]
    (leftUnit : LeftUnit M) (assoc : BindAssoc M)
    (rightUnit : RightUnit M) (handler : Handler S M) :
  ∃ map : {A : Type uAns} → Program S A → M A,
    (IsMonadMorphism S map ∧
      ∀ operation : S.Op,
        map (Program.perform operation) = handler.handle operation) ∧
    ∀ other : {A : Type uAns} → Program S A → M A,
      IsMonadMorphism S other →
      (∀ operation : S.Op,
        other (Program.perform operation) = handler.handle operation) →
      ∀ {A : Type uAns} (program : Program S A),
        other program = map program

theorem interpret_pinned [Monad M]
    (candidate : Handler S M → {A : Type uAns} → Program S A → M A)
    (morphism : ∀ handler,
      IsMonadMorphism S (fun {_A} program => candidate handler program))
    (operations : ∀ (handler : Handler S M) (operation : S.Op),
      candidate handler (Program.perform operation) = handler.handle operation)
    (handler : Handler S M) (program : Program S A) :
  candidate handler program = interpret handler program

def Handler.through [Monad M]
    (upper : Handler S (Program T)) (lower : Handler T M) : Handler S M

theorem interpret_through [Monad M] [LawfulMonad M]
    (upper : Handler S (Program T)) (lower : Handler T M)
    (program : Program S A) :
  interpret lower (interpret upper program) =
    interpret (upper.through lower) program

theorem Handler.through_assoc [Monad M]
    (leftUnit : LeftUnit M) (assoc : BindAssoc M)
    (first : Handler S (Program T))
    (second : Handler T (Program U))
    (last : Handler U M) :
  (first.through second).through last =
    first.through (second.through last)

theorem Handler.through_identity_right (handler : Handler S (Program T)) :
  handler.through (identityHandler (S := T)) = handler

theorem Handler.through_identity_left [Monad M]
    (rightUnit : RightUnit M) (handler : Handler S M) :
  (identityHandler (S := S)).through handler = handler

theorem Handler.through_endomorphism_monoid
    (first second third : Handler S (Program S)) :
  (first.through second).through third = first.through (second.through third) ∧
  first.through identityHandler = first ∧
  identityHandler.through first = first
```

The main ergonomic theorems use `[LawfulMonad M]`. Sharp companion theorems
may accept only the equations they consume (`LeftUnit`, `RightUnit`, and
`BindAssoc`). The weaker forms are not permission to call every bare `Monad`
lawful.

### Universe policy

For a fixed signature `S : Signature.{uOp,uAns}`, both every answer and every
program result are in `Type uAns`, and every handler target has kind
`Type uAns → Type v`. This alignment is intentional. It removes Foldlab's
constructible-but-not-interpretable shape: a `Program S A` cannot be formed at
a result universe which the target `M` cannot consume.

A client needing larger results declares or explicitly lifts a signature at
the larger answer universe. Mixed-universe sum is not silently inserted in
this slice. Any later `Signature.lift` must come with program/handler
translations and both round trips; it is not an implicit coercion.

## REQUIRES

- Lean toolchain is exactly `leanprover/lean4:v4.33.1`.
- The package depends on Lean core and Std only for this slice, unless a
  separately pinned dependency acceptance record is committed first.
- All signatures combined by `sum` share the same answer universe.
- Target `M` is a `Monad` for interpretation and satisfies exactly the monad
  equations named by each theorem.
- Effect4 imports no Foldlab module; Foldlab source is provenance and an
  external compatibility target only.

## ENSURES

Each law has a stable ID used by the falsifier table.

- `E4-ALG-L01` — program left unit:
  `bind (pure a) f = f a`.
- `E4-ALG-L02` — program right unit:
  `bind p pure = p`.
- `E4-ALG-L03` — program associativity:
  `bind (bind p f) g = bind p (fun a => bind (f a) g)`.
- `E4-ALG-L04` — one operation followed by `k` reconstructs `vis`:
  `bind (perform op) k = vis op k`.
- `E4-ALG-L05` — interpretation preserves pure:
  `interpret h (pure a) = pure a`.
- `E4-ALG-L06` — interpretation preserves one operation:
  `interpret h (perform op) = h.handle op`.
- `E4-ALG-L07` — interpretation preserves bind:
  `interpret h (bind p f) = interpret h p >>= fun a => interpret h (f a)`.
- `E4-ALG-L08` — identity interpretation reconstructs syntax:
  `interpret identityHandler p = p`.
- `E4-ALG-L09` — a summed handler is determined by both projections; left
  and right operations use their corresponding handler, and those two
  equations uniquely determine the sum.
- `E4-ALG-L10` — signature injections preserve pure and bind, are injective,
  and interpretation through a summed handler commutes with injection.
- `E4-ALG-L11` — injection adequacy: the initial target instance pins any
  candidate satisfying the interpretation square to `Program.inl` or
  `Program.inr`; a favorable target alone is not enough.
- `E4-ALG-L12` — freeness: every monad morphism out of `Program S` is induced
  by exactly one handler, assuming the right-unit equation needed to recover
  handler operations.
- `E4-ALG-L13` — initiality is claimed only in the category of `S`-models:
  for a fixed handler, `interpret` is the unique monad morphism that agrees
  with that handler on operations. `Program S` is not claimed initial among
  bare monads.
- `E4-ALG-L14` — interpreter adequacy: morphism laws plus agreement on every
  single operation pin a candidate interpreter pointwise to `interpret`.
- `E4-ALG-L15` — handler towers collapse:
  `interpret lower (interpret upper p) =
   interpret (upper.through lower) p`.
- `E4-ALG-L16` — `through` is associative across typed source/intermediate/
  target signatures and has identity handlers as categorical units.
- `E4-ALG-L17` — `through` is a monoid only on endomorphisms
  `Handler S (Program S)`; cross-signature handlers form category-shaped
  composition, not one monoid carrier.
- `E4-ALG-L18` — universe closure: for fixed `S`, `Program S A` and
  `Handler S M` use the same input universe `uAns`; the mismatched form in the
  battery is rejected.

## DECREASES

- `Program.bind`, `Program.inl`, `Program.inr`, `interpret`, and the proofs of
  their laws recurse structurally on the input `Program`.
- No fuel participates in these definitions. There is no loop constructor in
  this slice.
- `Handler.sum` and `Handler.through` are non-recursive.
- Any implementation whose recursion is hidden behind a dependency must
  expose an eliminator/fold with the same structural termination argument.

## FRAME

- Reads: the pinned Foldlab source spans and the public Lean/Std interfaces.
- Writes for the builder: only `Effect4/Algebra/**` and matching builder-owned
  test-runner wiring.
- Breaker-owned, read-only to the builder: this packet,
  `Effect4Test/Algebra/ExtractionContract.lean`, and the counterexample rows.
- Must not change: Foldlab files, CAS-specific types or semantics, Effect4
  Schema/Flow/Runtime modules, generated bytes, TypeScript surfaces, or the
  central counterexample IDs.
- Pure functional frame: no state, IO, clock, scheduler, `Lean.Expr`, or host
  runtime object enters the generic algebra.

## FALSIFIER

| Law | Exhibit that kills it | Executable site |
| --- | --- | --- |
| L01 | `a,f` with `bind (pure a) f ≠ f a` | `ExtractionContract.lean`, lawful-monad snapshot |
| L02 | `p` with `bind p pure ≠ p` | same |
| L03 | `p,f,g` whose two bind associations differ | same |
| L04 | `op,k` with `bind (perform op) k ≠ vis op k` | same |
| L05 | `h,a` with `interpret h (pure a) ≠ pure a` | same |
| L06 | `h,op` with `interpret h (perform op) ≠ h.handle op` | concrete state-handler case |
| L07 | `h,p,f` whose interpreted bind square does not commute | two-operation state-handler case |
| L08 | `p` with `interpret identityHandler p ≠ p` | public theorem snapshot |
| L09 | a sum handler that swaps or discards one branch while passing the other projection | concrete `swappedSum` witness; `E4-ALG-CE-001` |
| L10 | an injection that drops/reorders syntax, fails a monad law, is non-injective, or changes interpretation | theorem snapshots and concrete left injection |
| L11 | `ι ≠ inl` satisfying only a weakened/favorable interpretation condition | initial-target uniqueness snapshot; `E4-ALG-CE-002` |
| L12 | a monad morphism with no inducing handler, or two inducing handlers | free-property snapshot; axiom audit required |
| L13 | two distinct monad morphisms into one bare monad refuting unqualified initiality | `E4-ALG-CE-003` |
| L14 | (a) interpreter ignores `h` but preserves monad structure, or (b) agrees on operations but drifts on a two-op program | `E4-ALG-CE-002/003`; both hypotheses are required |
| L15 | `upper,lower,p` whose nested and composed interpretations differ | concrete state-handler tower and theorem snapshot |
| L16 | typed `upper,middle,lower` with unequal associations or failed identity | category theorem snapshots |
| L17 | a cross-signature pair for which the alleged monoid binary operation is ill-typed | `E4-ALG-CE-004` |
| L18 | `Small : Signature.{0,0}` and `Program Small Type` elaborates | guarded elaboration rejection; `E4-ALG-CE-005` |

Battery red command, before implementation:

```text
lake env lean Effect4Test/Algebra/ExtractionContract.lean
```

Expected current result: nonzero at the first missing
`Effect4.Algebra.Signature` import. After the builder supplies the frozen
surface, this same file must elaborate with no messages. Axiom inspection of
all exported theorem declarations and a clean `lake build` are additional
acceptance gates; successful elaboration alone is not the final claim.

## Closure graph

No cutover row closes until all incoming edges below are green.

```text
Signature.sum
  -> Handler.sum projections -> Handler.sum uniqueness
  -> Program injections -> injection morphism laws
     -> interpretation/injection squares -> injection uniqueness

Program constructors -> bind -> LawfulMonad
  -> interpret constructor equations -> interpret_bind
  -> IsMonadMorphism -> existence + handler uniqueness
  -> freeness + initiality-in-S-models + interpreter pin

identityHandler + interpret_bind
  -> Handler.through -> interpret_through
  -> category associativity + left/right identity
  -> endomorphism-only monoid

Signature answer universe = Program result universe = Handler input universe
  -> every constructible Program is in the domain of its Handler kind
```

## Breaks

No implementation has yet been attacked. Add only witnessed break records in
the `BROKE / LAW / WITNESS / CLASS / FIXED-BY` format; never delete them.
