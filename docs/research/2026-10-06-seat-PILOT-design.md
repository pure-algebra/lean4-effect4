# 2026-10-06 seat PILOT design: the fiber rule as a guarded lifted rule

Status: research note (history, not authority). Base: `9d50ac20`. Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-pilot-brief.md`. Decisions rows 285, 292 and
293.

## Question

`fiberTy` (`src/Effect4/Program/Typing/Rules.lean`) reads the head of a raw type. How does it
become the guarded rule of its member rule, so that each later conversion writes the same few
lines?

The dictionary has the words union member, member rule, lifted rule and eliminator
(`docs/core/controlled-english.md`). One word is new here: the **guarded rule** of a member
rule. It is the lifted rule where the target's normal form has at most one union member. It
refuses every other target.

## What was read or run (each with its evidence word)

| What | Evidence |
| --- | --- |
| The brief's reading list; the seven sites of `Checker.check`, the nine rules of the judgment and the nine inversions that name `fiberTy` | reading |
| The guard, its laws, the contract, the instance, the upper form and a use site, against the base build | proved in scratch: the kernel accepted each theorem at `[propext, Quot.sound]`; no gate has read one |
| The closed program of finding 6 | tested: ten guards, at the base |
| The differential at the base, 473 rows | tested: 128 of the 400 generated programs and all 73 programs of the truth lane are admitted |
| The statements that name `fiberTy`, at the base | tested: 26, by a producer that reads the environment |
| The uses of `fiberTy_eq_some` in `src/Effect4/Laws/Program/Typed/Denotation.lean` | reading: 11 rewrites and 2 comments |

The probes are filed beside this note: `docs/research/2026-10-06-seat-PILOT-probe-design.lean.txt`
with its output, and `docs/research/2026-10-06-seat-PILOT-probe-example.lean.txt`.

## Findings (each with its evidence)

### 1. The guard and its laws (proved in scratch)

```lean
def liftOne (rule : Ty → Option α) (target : Ty) : Option α :=
  if target.normalize.members.length ≤ 1 then lift rule target else none

theorem liftOne_eq_some_iff :
    liftOne rule t = some a ↔ t.normalize.members.length ≤ 1 ∧ lift rule t = some a
theorem liftOne_some : liftOne rule t = some a → lift rule t = some a
theorem liftOne_eq : t.normalize.members.length ≤ 1 → liftOne rule t = lift rule t
theorem liftOne_congr : s.normalize = t.normalize → liftOne rule s = liftOne rule t
theorem liftOne_never : liftOne rule .never = some Answer.bot
theorem liftOne_member : Ty.Normal t → t.isMember = true →
    liftOne rule t = (rule t).map (Answer.join Answer.bot)
theorem liftOne_two : 1 < t.normalize.members.length → liftOne rule t = none
```

The definition stands beside `UnionRule.lift` (`src/Effect4/Program/UnionRule.lean`). The laws
stand in the law module (`src/Effect4/Laws/Program/UnionRule.lean`). The first law is the whole
meaning of the guard. `liftOne_some` carries each law whose premise is an answer of the lifted
rule.

### 2. The contract of a guarded eliminator (proved in scratch)

Each statement holds for every `Eliminator rule C`, so no conversion proves one again.

```lean
theorem Eliminator.liftOne_upper : liftOne rule t = some a → Ty.subN t (C a) = true
theorem Eliminator.liftOne_least :
    liftOne rule t = some a → Ty.subN t (C b) = true → le a b
theorem Eliminator.liftOne_answers : rule t = some a →
    ((∃ a', liftOne rule t = some a' ∧ le a a' ∧ le a' a) ↔ t.normalize.members.length ≤ 1)
theorem Eliminator.liftOne_isSome_iff : (liftOne rule t).isSome = true ↔
    t.normalize.members.length ≤ 1 ∧ ∃ b, Ty.subN t (C b) = true
theorem Eliminator.liftOne_mono : Ty.subN s t = true → s.normalize.members.length ≤ 1 →
    liftOne rule t = some b → ∃ a, liftOne rule s = some a ∧ le a b
theorem Eliminator.liftOne_laws : …   -- the four parts of the brief, as one statement
```

- **The exact member premise.** Let the member rule answer at a raw type. The guarded rule
  answers there exactly when that type's normal form has at most one union member. The three
  facts of `Eliminator` do not give that premise. A product is the red control: the normal form
  of `prod (nat | string) unit` has two union members (tested). The fiber constructor has the
  premise, because the normal form of a fiber type is a fiber type (`Member.fiber_one`).
- **Two statements go beyond the brief's four.** `liftOne_isSome_iff` says where the guarded
  rule answers. `liftOne_mono` says what the guard keeps of the monotone law: the smaller target
  must have at most one union member.

### 3. The rule, in one line, and its instance (proved in scratch)

```lean
def Member.fiber : Ty → Option (Ty × Ty)       -- the by-shape function of today
  | .fiberOf value error => some (value, error)
  | _ => none
def fiberTy : Ty → Option (Ty × Ty) := UnionRule.liftOne Member.fiber

theorem Member.fiber_eliminator : Eliminator Member.fiber (Function.uncurry Ty.fiberOf)
theorem fiberTy_upper : fiberTy t = some pair → Ty.subN t (.fiberOf pair.1 pair.2) = true
theorem fiberTy_fiberOf :
    fiberTy (.fiberOf value error) = some (value.normalize, error.normalize)
```

- The judgment, the inversions and the checker name `fiberTy`, and none looks inside it. So no
  statement of `HasTy.lean`, of `Typing/CheckInversion.lean` or of `Checker.lean` changes its
  text. The base's list holds 26 statements, and the head's list is compared with it.
- The instance and the rule's facts stand in a new law module,
  `src/Effect4/Laws/Program/Eliminators.lean`, in one section for the fiber rule. The contract
  stands once, in the law module of the combinator.
- `fiberTy_fiberOf` states the change of spelling. The old rule answered the raw columns of a
  fiber type. The converted rule answers their normal forms.

### 4. The shape lemma and a use site (proved in scratch)

`fiberTy_eq_some` (`src/Effect4/Laws/Program/Typed/Membership.lean`) is false of the converted
rule, so it goes. Each of its 11 rewrites becomes one line after the term is evaluated.

```lean
-    rw [fiberTy_eq_some hfib] at hty
     obtain ⟨v, hv, hfit⟩ := evalTerm_progress_env henv hty
+    replace hfit := fits_subN w (fiberTy_upper hfib) v hfit
```

Four of the 11 sites read a list of handles through `Checker.listOf?`. They wrap the upper form
in `subN_list`, a new lemma on the order of two list types.

### 5. The differential (tested at the base)

One producer writes a row for each program of the two corpora. A row holds the verdict, then the
type or the refusal, as the checker spells it and at its normal form. The base's output is
filed, and the head's output is compared with it. At the base no generated program is refused
with `notFiber` at `never`. The 48 such refusals hold `nat`, `bool`, `unit`, `string`, a product
and an exit type.

### 6. A closed program that the converted rule refuses (tested at the base)

```text
fiber   = fork( x = (true ? 1 : "s");  succeed(cons(pair("k", x), nil)) )
entries = join(fiber)
succeed(mapFromEntries(entries))
```

- The body's answer is `list (prod (lit "k") (nat | string))`. That type is not its own normal
  form: the normal form distributes the product over the union.
- Today the checker admits the program, at `map string (nat | string)`.
- The converted rule answers the normal form of the value column: a list of a union of two
  products. The scheme of `mapFromEntries` binds its parameter at the first union member,
  `nat`, and it refuses the type. So the converted checker refuses the program.
- The base holds no converted rule, so the probe checks the last line in the two environments.
  The head's battery pins the whole program.
- The rule is not changed to avoid the refusal. The cause is the match of a template, which
  seat BOUNDS probes.

### 7. The case-site policy (reading)

The policy pins `Effect4.Program.fiberTy` as a case site on `Ty`
(`tools/Conform/Effect4/cases-policy.json`). The conversion moves the match to `Member.fiber`.
So `make check-cases` is expected to refuse the head until the policy is pinned again. The seat
does not edit the policy. The receipt gives the refusal lines and the seeded policy.

## Proposals (not rulings)

1. **Names.** The guard is `UnionRule.liftOne`, as seat UNION's receipt names it. The member
   rule is `Member.fiber`. The instance is `Member.fiber_eliminator`, because it is a fact of
   the member rule.
2. **Homes.** The guard's laws and the contract extend the law module of the combinator. Each
   converted rule has one section of `src/Effect4/Laws/Program/Eliminators.lean`. Its controls
   stand in a new battery, `Test/Program/Eliminators.lean`.
3. **The order of the commits.** The guard lands with its laws as planned goals, and then
   the proofs land in place. The conversion follows, with the instance, the shape lemma and the
   11 uses. The controls and the cut are last.
4. **The cut.** The five theorems of seat UNION's receipt go in a commit of their own.

## What this does not establish

- No file of the tree holds a statement of this note yet. A theorem proved in scratch was
  accepted by the kernel in a scratch file, and no gate has read it.
- The guarded rule is not monotone at a proper union, so `checker-monotone` stays open there.
- The differential is a finite check of 473 programs. Finding 6 shows that an admitted program
  can become refused.
- Nothing here says what tsgo accepts. This seat runs no TypeScript.
- The host boundary stays where `docs/core/host-boundary.md` puts it.
