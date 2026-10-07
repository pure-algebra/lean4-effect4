# 2026-10-06 seat FORM: the design of formation at a type variable

Status: a design note (history, not authority). Base: `ea0f584a`, branch `seat/form`. It rules
nothing. The brief is `docs/research/2026-10-05-claude-lead/briefs/seat-form-brief.md`.

## 1. The clause

`Formation.HeadFormed` (`src/Effect4/Program/Formation.lean`) gains one alternative:

```lean
  | .var _ => template = true
```

Formation knows a template by the flag of the site, `Formation.Site.template`. The collector
sets it, and no rule reads the site's path.

| Collector | Flag | What it holds |
| --- | --- | --- |
| `Formation.tableSites` | `true` | the three columns of each supplied row |
| `Formation.instantiatedSites` | `false` | the three columns of a row after substitution |
| `Formation.programSites` | `false` | each annotation of a program |
| the record rule of `argTy` (`src/Effect4/Program/Typing/Rules.lean`) | `false` | a record term's declaration |

An annotation is a record's declaration, a list fold's stated accumulator, a loop's cursor
type, and an operation's binder term and type arguments (`Formation.argumentAnnotations`). So
the clause refuses both programs of the brief. An atom's scheme is no formation site.

Two rules of the checker read strict formation, so the checker itself narrows too. The term
typer refuses a record declaration that holds a variable. The row rule refuses an instantiated
column that holds a variable.

## 2. The reason, and what an appended reason moves

`FormationReason` gains `typeVariable`, appended last. `Formation.reason` answers it at a
variable. The refusal keeps the raw type, so the reason carries no index.

| What moves | Producer or owner |
| --- | --- |
| `src/Effect4/Api/RefusalsDerived.lean`: the reason's `Canonical` instance | `python3 scripts/generate.py --only derived` (manifest group `Refusals`) |
| `tools/Effect4Gen/guards/refusals.lean`: the guard list `formationReasons` gains the reason | by hand; the generator appends the file |
| `tools/Conform/Effect4/cases-policy.json`: two rows, `Formation.instDecidableHeadFormed` and `Formation.reason`; `var` leaves each default's cover | the coordinator pins; the seat gives the refusal's lines |
| `generated/semantics.md`: the new placed theorems | `make gen-semantics`, the coordinator's |
| `Test/Program/FormationContract.lean`: the pin of decisions row 212, admitted to refused | the seat; a verdict that moves |
| `Test/Codegen/TermRows.lean`: one module refusal moves from the printer to formation | the seat; a verdict that moves |

Five things do not move: the wire tags, the OCaml mirrors, the TypeScript mirrors, the host
protocol and the baseline policy. The evidence is a search of the tracked tree for the
alphabet's names.

## 3. `check_closed`, as Lean elaborates it

Compiled in scratch at the base, as a `def … : Prop`:

```lean
structure ClosedSig (sig : Signature Op) : Prop where
  atom : ∀ (name : String) (tys : List Ty) (ty : Ty), sig.atomOf name tys = some ty →
    (∀ t ∈ tys, t.closed = true) → ty.closed = true
  service : ∀ (key : ServiceKey) (ty : Ty), sig.serviceTy key = some ty → ty.closed = true

theorem check_closed [ScopedOp Op] (sig : Signature Op) (closed : ClosedSig sig) {env : TyEnv}
    (henv : ∀ t ∈ env, t.closed = true) {p : List Nat} {e : Eff Op} {t : EffTy}
    (formed : Formation.Formed (Formation.programSites e))
    (h : Checker.check sig env p e = .ok t) :
    t.answer.closed = true ∧ t.error.closed = true
```

The premises, each with its reason:

- **A closed environment.** A variable of a term has the environment's type.
- **Closed atoms.** An atom's answer is not a formation site. The native table has the property.
- **Closed service carriers.** `Effect.service(key)` answers the carrier as it is declared.
- **No premise on a row.** The study asked for well-scoped rows. The row rule checks strict
  formation of each instantiated column, and strict formation now implies a closed type.

**A finding (compiled in scratch, a finite check).** The admission of a typing signature does
not give closed service carriers. `flatCarrier` (`src/Effect4/Program/SigApp.lean`) accepts `refOf t` at
every `t`, and a declared carrier is no formation site. So `Effect.service` at a declared
carrier `Ref<T3>` is a third program of one node: `admitSig` and `admitProgram` admit it at
`Ref.Ref<T3>`. The clause does not reach it. The seat keeps the premise, and gives the options
in the receipt.

## 4. The proof's shape

- `hasTy_closed` over the six judgments of `HasTy`, one line per rule, and `check_closed` by
  `check_sound`.
- One lemma per type operation: `normalize` (landed), `join`, `instantiate` at closed bindings,
  `infer`, the tag residuals, the record and tuple rules, an atom's scheme.
- The premise on annotations enters as a fold of the program. One general law of the generated
  positional fold relates it to `Formation.programAnnotations`. Through a homomorphism that
  reads no position, a positional fold is the plain fold. It is one line per sort (proved in
  scratch for the nine sorts of terms and programs).

## 5. After the coordinator's answer (the same day)

The coordinator accepted the design and gave four answers.

1. The carrier is taken into the slice, as its own step and its own commit. A declared service
   carrier becomes a strict formation site. The corollary of `check_closed` for an admitted
   program then has no premise on the signature.
2. The change of row 212's pin is right. The seat searches `Test/contracts/` for a sentence
   that states the old behaviour, and does not edit a packet.
3. The lemma for a rule that reads a union member by member is stated over the explicit shape.
   The two record instances are proved by `show` to that shape.
4. `ClosedSig (nativeSignature table)` is proved. A loop's cursor type and a fold's accumulator
   type at `nat | T2` are red controls too.
