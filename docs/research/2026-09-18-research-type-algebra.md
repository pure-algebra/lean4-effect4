# The type algebra of the stored-program language: what the compiler world knows, as Lean 4 designs (2026-09-18)

Research seat, read-only. Topic: the problems the `Ty` push keeps hitting — applications and
records without a nested inductive, variance, template inference, a top type, canonical forms —
against what compilers and type-system research already settled, translated into designs that
use Lean 4.33.1's own instruments (derived instances, generated folds, `termination_by
structural`, well-founded recursion, `Std`'s order classes, aesop) instead of fighting them.

## 0. What this note stands on

Every claim about this tree is **read** from the cited file and line. No Lean ran in this seat:
the compiler lock is the main session's, so no cost figure for a design that does not yet exist
is measured — those are **assumed** and marked. Claims about Lean itself are read from the
toolchain source at `~/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean`. Claims about
TypeScript are read from the checker on disk, `ts/eff/node_modules/typescript/lib/typescript.js`
at version 5.9.2 (`package.json`), which is the compiler the corpus lane runs. Claims about
LLVM, MLIR, Flow and CDuce are from the literature and are marked **assumed** where I could not
read the source here.

The tree moved under this seat: it was read first at `02e7d4f0` (rows 42/43 step 2 landed), and
`Ty.unknown` (decisions row 46) plus the release and snapshot typings of row 47 landed during the
writing. §4 is therefore a review of what landed rather than a proposal, §2's measurement is
quoted at the new count, and every `Ty.lean`, `TypeAlgebra.lean` and `Typed.lean` line number is
the post-landing one.

Six facts about Lean 4.33.1 govern every encoding question in §1, and all six are read:

| # | fact | where |
| --- | --- | --- |
| F1 | `deriving DecidableEq` **refuses** a nested inductive outright: `if indVal.isNested then return false` | `Lean/Elab/Deriving/DecEq.lean:211-212` |
| F2 | `deriving DecidableEq` **works** for a non-nested *mutual* block: it emits one aux function per member inside a `mutual`, each closed `termination_by structural` | `Lean/Elab/Deriving/DecEq.lean:180-199` |
| F3 | `deriving Repr` emits `partial def` whenever the block is nested **or** has more than one member (`usePartial := indVal.isNested \|\| typeInfos.size > 1 \|\| …`) | `Lean/Elab/Deriving/Repr.lean:98-105`, `Lean/Elab/Deriving/Util.lean:116` |
| F4 | this repo's trust gate rejects `partial` anywhere in `src`, with a pinned red fixture | `scripts/test-trust-gate.sh:3`, `:302` |
| F5 | structural recursion **does** go through a nested container position, via companion functions in the same block (`termination_by structural`); the generator already relies on it | `src/Effect4/Schema/Fold.lean:128-171` |
| F6 | well-founded recursion through a nested `List` is supported by core: `List.sizeOf_lt_of_mem` plus a `decreasing_trivial` extension whose docstring names `inductive T \| mk : List T → T` | `Init/Data/List/BasicAux.lean:230-246` |

Two consequences are worth stating before the sections, because they cut differently from the
way the plan's §1 states the trap. A nested `Ty` does **not** lose structural recursion (F5, F6);
it loses (a) derived decidable equality (F1), (b) a non-`partial` derived `Repr` (F3 with F4),
and (c) the `induction` tactic's automatic hypotheses for children under the container — which
is the expensive one, because every proof then fans out into a mutual block with one theorem per
container position. And the tree has already paid that bill once, in full, where it can be read:
`Representation` is mutual *and* nested (`List Representation` in four constructors,
`src/Effect4/Schema/Representation.lean:701-778`), so its decidable equality is hand-built as
nine mutual Boolean functions plus nine mutual agreement theorems, 255 lines
(`:812-1067`), with the module's own note: "`deriving DecidableEq` has no handler for a mutual
nested inductive on Lean 4.33.1" (`:797-806`), and `Repr` and `Inhabited` deliberately dropped
(`:525-528`). Lean core does the same thing for its own nested `Json`: `deriving Inhabited` only,
and `private partial def beq'` (`Lean/Data/Json/Basic.lean:180-191`) — the `partial` this repo's
gate refuses.

So the question in §1 is not "nested or not". It is: **which of three encodings pays which of
those three bills**, and the tree already contains a worked example of each.

---

## 1. Applications, records and variants without the nested-inductive trap

### 1.1 What the outside world does

Five encodings are in production use, and they split by what they are optimising.

**Interned DAG with an argument array (LLVM, MLIR).** LLVM's type system is a hash-consed DAG:
a type is a pointer, structural equality is pointer equality, and the argument list is an
`ArrayRef`. Literal struct types are uniqued on their element list in the context; identified
struct types are *nominal* and never uniqued, precisely so that a recursive type can name
itself. MLIR generalises this to every attribute and type through `TypeID` and storage
uniquing in the context. The cost is that equality is no longer a structural function you can
reason about: it is an invariant of the allocator. (**assumed**: read from the LLVM language
reference and the MLIR design papers, not from source on this machine.)

**Interned node with a type-argument array and a reference to a declaration (TypeScript).** A
`TypeReference` carries a `target` (the declaration) and a resolved type-argument array, and
interning is by a list id (`getTypeListId`). Equality is identity; assignability is a separate
relation with a cache. Object types are *not* applications at all: they are property tables.
Read on disk at the union side — `addTypeToUnion` inserts into a set sorted by the interned
`type.id` with a binary search (`typescript.js:65825-65844`).

**Spine encoding.** A curried application `T A1 … An` as nested binary nodes:
`app (app (app T A1) A2) A3`. This is what Lean's own `Expr` does (`Expr.app f a`), and what
GHC Core does. It keeps the inductive binary, hence non-nested, hence everything derives; the
price is that "the head and its n arguments" is a *view*, computed by a spine walk, and every
arity error becomes a runtime `Option` rather than a type error.

**Arity-indexed families.** `app : (n : Nat) → Vector Ty n → Ty`. `Vector` in this toolchain is
a structure over `Array`, so this is nesting through `Array` — the worst case for F1/F3 and,
unlike `List`, without the `decreasing_trivial` support of F6. A genuinely indexed alternative
(`app : Sig → (Fin (arity s) → Ty) → Ty`) turns the argument list into a *function*, which the
OCaml projection refuses by construction: `Conform.Source.readShape` has no function case and
throws "unsupported field" (`tools/Conform/Source/Description.lean:35-54`). Dead on arrival for
this estate.

**Mutual spine sibling.** A dedicated inductive for the list of children, mutual with the parent:
`Ty` and `TyArgs`, where `TyArgs := nil | cons (head : Ty) (tail : TyArgs)`. Non-nested, so F1 is
satisfied (F2 gives derived equality for the whole block); `induction` gives proper hypotheses on
both; the fan-out per proof is 2, not 9.

**And this last one is what the tree already chose, twice.** `Eff`'s block has `Effs`, `Stmts`
and `LayerTerms` as exactly this spine idiom rather than `List (Eff Op)`, and the whole seven-member
block gets `deriving instance DecidableEq for Eff, Stmt, Stmts, Effs, ActionTerm, LayerTerm,
LayerTerms` (`src/Effect4/Program/Eff.lean:348-419`); `Term` has `Terms` the same way
(`:83-102` of `Typing/Rules.lean` types them as one mutual fold). No `Repr` is derived for that
block — consistent with F3.

### 1.2 The four encodings against the eight things that must survive

Scored for `Ty` at HEAD: a plain 20-constructor inductive with `deriving DecidableEq, Repr`
(`src/Effect4/Program/Ty.lean:23-59`), sixteen folded traversals
(`src/Effect4/Program/Folds/Ty.lean:23-38`), `sub` by well-founded recursion on
`sizeOf a + sizeOf b` (`Ty.lean:421-440`), a canonical-form invariant `Normal` (`:571-594`), an
injective key (`:130-150`, injectivity at `:237-260`), 20 wire tags
(`tools/Effect4Gen/wire-tags.json`), and an OCaml alphabet emitted from the declaration
(`src/OCaml5/Eff/Emit.lean:366-385` with `src/OCaml5/Eff/World.lean:105-119`).

| what must survive | A. dedicated constructors (today) | B. mutual spine sibling | C. nested `List Ty` | D. spine (binary `app`) |
| --- | --- | --- | --- | --- |
| `deriving DecidableEq` | kept | kept (F2) | **lost** (F1) → ~255 lines by hand, as `Representation` shows | kept |
| `deriving Repr` | kept | **lost** as non-`partial` (F3+F4) → one hand-written mutual `Repr`, ~20 lines; `Row` derives `Repr` and has three `Ty` fields (`Eff.lean:192-215`), so it cannot simply be dropped | lost the same way, plus F1 | kept |
| structural `induction` with hypotheses | per constructor | on two motives; each `Ty` induction becomes two theorems | **no hypotheses under the container**; each becomes a mutual block, one theorem per container position | per constructor, but the head/argument split is a view, so every proof carries a spine lemma |
| `sizeOf` termination for `sub` | works today | works; one `sizeOf` lemma for the spine | works via F6 (`sizeOf_list_dec`) | works, but `sub` must recurse on the spine and *then* compare heads |
| `Normal` | one arm per constructor | one arm plus a spine predicate | one arm with a `∀ x ∈ args` clause | one arm; the "no union under a `prod` head" condition becomes a spine condition |
| `key` injectivity | one arm; `append_inj` per binary node | one arm; the spine needs a length prefix, exactly as `prod` does today (`:141`) | same, with a list fold | the spine makes the key longer; injectivity unchanged |
| wire + OCaml emitter | append tags | append tags; `Shape.nominal` sees the sibling (`Description.lean:50-54`), OCaml gets a second type in the group | `Shape.list` already exists (`:46`), OCaml gets `ty list` (`World.lean:57`) | append tags |
| generated fold | `TyAlgebra` + monadic half (`Fold.lean:31-51`, `:327`) | two-member `TyFam`, as `TermFam` is (`Fold.lean:597-622`) | works — `RepresentationAlgebra` is exactly this (`Schema/Fold.lean:20-44`) — but the generator emits **no monadic half** for a block with a composite position (manifest note, `tools/Effect4Gen/manifest.json`, SchemaFold group); `TyMAlgebra` has no consumer today, so this is a paper loss | works |

### 1.3 Recommendation

**Keep A for handle sorts. Use B — a mutual spine sibling — when records and variants land
(decisions row 2), and keep `Ty.app` off the table.**

Concretely, for row 2:

```lean
mutual
  inductive Ty
    | never | unknown | unit | nat | int | string | bool
    | handle (target : String)
    | option (inner : Ty) | list (inner : Ty)
    | prod (left right : Ty) | except (error value : Ty)
    | exitOf (value error : Ty) | causeOf (error : Ty) | fiberOf (value error : Ty)
    | union (left right : Ty) | lit (value : String)
    | refOf (value : Ty) | deferredOf (value error : Ty) | var (index : Nat)
    /-- `{ f₁ : T₁, … }`: fields ascending by name, the invariant `Normal` carries. -/
    | record (fields : Fields)
    /-- `{ _tag: "c₁", … } | …`: the same spine, read as a variant. -/
    | variant (cases : Fields)
  /-- The field spine: `Effs`/`Stmts`/`Terms`' idiom, not `List (String × Ty)`. -/
  inductive Fields
    | nil
    | cons (name : String) (type : Ty) (rest : Fields)
end
deriving instance DecidableEq for Ty, Fields
```

Why this and not the alternatives, in the estate's own terms:

- It is the **idiom that is already proved to work here** three times over (`Effs`, `Stmts`,
  `LayerTerms`, `Terms`), including through `deriving instance DecidableEq` on a seven-member
  block, the wire generator, the OCaml emitter and `fold_of`'s list-sibling shape
  (`src/Effect4/Program/FoldOf.lean:28-31`). Nothing new has to be taught to any instrument.
- It costs exactly **one hand-written `Repr`** (F3), and that is a 20-line mutual structural
  definition, not a `partial` one, so the trust gate stays green. Assumed, not measured.
- Every `Ty` induction becomes **two** theorems, not nine. `Representation` is the measured
  upper bound of the nested route: nine functions and nine theorems for one property.
- `Fields` gives the canonical-form invariant somewhere to live: "ascending by name, no
  duplicate" is a `Fields`-level predicate, and the estate already has the machine for exactly
  that shape — `Effect4.Row` is a list plus `Ascending` (`src/Effect4/Data/Row.lean:30-33`) with
  the antichain filter generic in a Boolean relation (`:277`, `:342`). A `Row (String × Ty)`
  field is tempting and should be **refused**: `Row` is a structure with a proof field, and the
  wire generator's own note says an applied carrier with a proof field needs a hand instance
  (manifest, Runner group). Keep the proof out of the carrier, as `Normal` already does
  ("an erased proof invariant, not another stored type representation", `Ty.lean:6-9`).
- `Ty.app name args` (decisions row 3) stays refused, and for a better reason than the plan
  gives. The plan says a `List Ty` argument makes `Ty` nested; true, but B shows nesting is not
  forced. The real objection is **semantic**: `app` is a nominal head with no variance
  declaration and no arity check, so `sub`, `Normal` and `key` would all need a side table keyed
  by name — which is precisely the variance table of §2, except keyed on an unbounded string
  instead of a closed constructor set. Row 3 exists for one purpose, reading a *foreign* schema
  (row 1), and for that purpose the honest encoding is a distinct constructor, `Ty.foreign
  (id : String) (args : Fields)`, whose `sub` is invariant in every argument and whose `hasTy` is
  `false` — an opaque nominal type, not a type constructor. That keeps every law of §2 true
  without a name-keyed table.

The one thing B does not do is make `Ty` cheaper to extend *today*, and it should not be done
speculatively: the push's L1–L7 all fit in A, so **B lands with row 2 and not before**.

---

## 2. Variance as a table, and the laws proved once

### 2.1 The chore, measured

`sub` is a hand case table with a reflexivity fast path (`Ty.lean:421-440`). Three proofs in
`Laws/Program/TypeAlgebra.lean` enumerate its arms, and step 2 of the push added the same
invariant alternative to each of the three: `sub_trans_core` (`:34-38`),
`sub_antisymm_normal` (`:522-528`), `sub_normalize_of_sub` (`:774-777`). The plan's own note
records it as "the same chore three times, so a `sub` induction principle that hides the arm
shapes is owed to the bank" (`2026-09-18-rows-42-43-plan.md` §2b(3)).

The larger chore is `hasTy_sub` (`src/Effect4/Program/Typed.lean:144-399`): 256 lines, of which
**sixteen** are copies of the same five-line block

```lean
      | union b1 b2 =>
        rw [Ty.sub_union_right (.refOf a1) b1 b2 rfl] at hsub
        obtain h1 | h2 := Bool.or_eq_true_iff.mp hsub
        · simp only [Val.hasTy, Bool.or_eq_true]; exact Or.inl (hasTy_sub (.refOf a1) b1 v allocated h1 hv)
        · simp only [Val.hasTy, Bool.or_eq_true]; exact Or.inr (hasTy_sub (.refOf a1) b2 v allocated h2 hv)
```

— once per constructor of the *left* type (sixteen `union b1 b2 =>` arms, sixteen
`sub_union_right` rewrites, counted in the file) — plus sixteen more copies of

```lean
      | _ =>
        revert hsub; unfold Ty.sub; simp only [heq, ↓reduceIte]; intro h; contradiction
```

There are 35 sites in `src` that unfold `Ty.sub`. A new constructor touches all of this, and the
owner's rule (a new constructor must never touch a proof) is currently kept by rewriting
catch-alls as wildcards — which works for proofs and, as §7.3 shows, silently breaks classifiers.

The count moved **while this note was being written**: `Ty.unknown` landed (§4) and took the
`union` block from fifteen copies to sixteen, plus a `first | exact absurd rfl hbu | (revert
hsub; …)` alternative in every one of the catch-alls (`Typed.lean:164-168`). That is the chore
arriving on schedule, and it is the strongest argument for doing §2's hoist before row 2 adds two
more constructors.

### 2.2 The design: a head/argument view plus a variance table

Nothing about `Ty` has to change. What changes is that `sub` is written **once**, over a view.

```lean
inductive Variance | co | contra | inv
deriving DecidableEq, Repr

/-- The head of a type: its constructor, without its type arguments. `union` and `never` are
    deliberately absent — they are the row structure, not heads (§2.3). -/
inductive Head
  | unknown | unit | nat | int | string | bool
  | handle (target : String) | lit (value : String) | var (index : Nat)
  | option | list | prod | except | exitOf | causeOf | fiberOf | refOf | deferredOf
deriving DecidableEq, Repr

/-- The one place variance is declared. rc.112's own declarations (decisions row 55):
    `Fiber<out A, out E>`, `Ref<in out A>`, `Deferred<in out A, in out E>`. -/
def Head.variance : Head → List Variance
  | .option | .list | .causeOf => [.co]
  | .prod | .except | .exitOf | .fiberOf => [.co, .co]
  | .refOf => [.inv]
  | .deferredOf => [.inv, .inv]
  | _ => []

/-- The head and the immediate arguments of a non-union, non-never type. -/
def Ty.view : Ty → Option (Head × List Ty)
  | .never | .union _ _ => none
  | .option t => some (.option, [t])
  | .prod a b => some (.prod, [a, b])
  | .refOf t => some (.refOf, [t])
  -- … one arm per constructor, mechanical
  | .nat => some (.nat, [])

/-- The primitive edges between argument-less heads: `lit s ≤ string` and the top edge
    (decisions row 46). A table, so `nat ≤ int` or a future numeric tower is a row, not a proof
    change. -/
def Head.base : Head → Head → Bool
  | _, .unknown => true
  | .lit _, .string => true
  | h, k => h == k
```

and then

```lean
mutual
  def subArgs : List Variance → List Ty → List Ty → Bool
    | [], [], [] => true
    | .co :: vs, x :: xs, y :: ys => sub x y && subArgs vs xs ys
    | .contra :: vs, x :: xs, y :: ys => sub y x && subArgs vs xs ys
    | .inv :: vs, x :: xs, y :: ys => sub x y && sub y x && subArgs vs xs ys
    | _, _, _ => false

  def sub (a b : Ty) : Bool :=
    if a = b then true
    else match a, b with
    | .never, _ => true
    | .union a1 a2, b => sub a1 b && sub a2 b
    | a, .union b1 b2 => sub a b1 || sub a b2
    | a, b =>
      match a.view, b.view with
      | some (ha, xs), some (hb, ys) =>
        (ha.base hb && xs.isEmpty && ys.isEmpty) ||
          (ha == hb && subArgs ha.variance xs ys)
      | _, _ => false
end
termination_by
  | subArgs _ xs ys => xs.foldl (fun n t => n + sizeOf t) 0 + ys.foldl (fun n t => n + sizeOf t) 0
  | sub a b => sizeOf a + sizeOf b
```

Termination needs exactly one new lemma, proved once by `cases a <;> simp [Ty.view]`:

```lean
theorem Ty.view_sizeOf {t : Ty} {h : Head} {args : List Ty} (hv : t.view = some (h, args)) :
    ∀ x ∈ args, sizeOf x < sizeOf t
```

### 2.3 Why `never` and `union` stay outside the table and `unknown` goes inside it

`never` and `union` are not type constructors; they are the *row* structure that `normalize`
maintains (`normalizeRow`, `Ty.lean:530-532`, over `Effect4.Row.antichain`). `sub`'s three
non-head rules — `never` below everything, a union on the left is a conjunction, a union on the
right is a disjunction — are the lattice rules, and they are the only arms that a proof over the
design above has to enumerate. That is the whole point: **three cases, forever**, whatever `Ty`
grows.

`unknown` is the asymmetric one, and the tree's own `members` already says which side it belongs
on. `never` is the empty union (`members .never = []`, `Ty.lean:105`), so its rule is *not*
memberwise: `sub never (union b1 b2)` must be `true`, and going through the union-right
disjunction would give `sub never b1 || sub never b2` with `never` as a head — false. `unknown` is
not a union at all (`members .unknown = [.unknown]`, `isMember .unknown = true`,
`Ty.lean:106`, `:392`), and its rule *is* memberwise on the left: a union is below `unknown`
exactly when every member is, which is what the conjunction arm computes. So `unknown` can be a
`Head` with one `base` row, and that is strictly cheaper than a fourth lattice arm — a `base` row
costs nothing in the generic proofs, a lattice arm costs one case in each. HEAD placed it as a
lattice arm (`Ty.lean:427-428`), which is right for a hand-written `sub` and would move into
`Head.base` under this design.

### 2.4 What is proved once, and how

Each law becomes a generic lemma about `subArgs` plus the three lattice cases.

```lean
theorem subArgs_refl (vs : List Variance) (xs : List Ty) (h : vs.length = xs.length) :
    subArgs vs xs xs = true
theorem subArgs_trans (vs : List Variance) (xs ys zs : List Ty) :
    subArgs vs xs ys = true → subArgs vs ys zs = true → subArgs vs xs zs = true
theorem subArgs_antisymm (vs : List Variance) (xs ys : List Ty)
    (hnormal : ∀ x ∈ xs, Normal x) (hnormal' : ∀ y ∈ ys, Normal y) :
    subArgs vs xs ys = true → subArgs vs ys xs = true → xs = ys
```

`subArgs_trans`'s three-way induction is uniform: at `co` it is `sub_trans`, at `contra` it is
`sub_trans` with the arguments swapped, at `inv` it is both. Written today, that is the three
alternatives step 2 added to `sub_trans_core` by hand, hoisted into one lemma with one
`Variance` case split — and the hoisting is what makes the *next* constructor free. The
`Head.base` table needs two obligations, both `decide`-able on the closed `Head` set once
`handle`/`lit`/`var` are given their string/nat arguments as parameters:

```lean
theorem base_refl (h : Head) : h.base h = true
theorem base_trans (h k l : Head) : h.base k = true → k.base l = true → h.base l = true
```

`hasTy_sub` is the one law that cannot be fully generic without a second step, and it is worth
being exact about why. `Val.hasTy` recurses on the *type* and inspects the value per head
(`Typed.lean:34-101`); monotonicity in an argument is therefore a per-head fact. The design that
makes it generic is to give `hasTy` the same view:

```lean
def Head.admits (h : Head) (v : Val) (args : List Ty) (allocated : List String)
    (rec : Val → Ty → Bool) : Bool
```

so that `Val.hasTy v t allocated = match t.view with | some (h, args) => h.admits v args allocated (…) | none => …`,
and then the single obligation per head is

```lean
theorem Head.admits_mono (h : Head) (v : Val) (xs ys : List Ty) (rec rec' : Val → Ty → Bool)
    (hargs : subArgs h.variance xs ys = true)
    (hrec : ∀ w x y, sub x y = true → rec w x = true → rec' w y = true) :
    h.admits v xs allocated rec = true → h.admits v ys allocated rec' = true
```

which is one line per head (`rfl`-ish for the coarse handle heads, `list_all_mono` for `list`,
`causeAdmits_mono_sub` for `causeOf`/`exitOf` — all three helpers already exist,
`Typed.lean:115-141`). The 16+16 copies of the union boilerplate collapse into the two union
cases of the generic proof. **Assumed**: 256 lines to roughly 70, and a new constructor costs one
`view` arm, one `variance` row and one `admits_mono` line, with no proof edited.

### 2.5 Where this connects to `Std`

`CTy` already carries `Std.IsPartialOrder` and `Std.LawfulOrderSup` with `max_le_iff` discharged
by the join laws (`TypeAlgebra.lean:854-864`); `Ty`'s key order carries `Std.IsLinearOrder` and
`Std.LawfulOrderLT` (`Ty.lean:373-384`). The classes available in this toolchain are
`IsPreorder`, `IsPartialOrder`, `IsLinearPreorder`, `IsLinearOrder`, `LawfulOrderLT`,
`LawfulOrderBEq`, `MinEqOr`/`MaxEqOr`, `LawfulOrderInf`/`LawfulOrderSup`,
`LawfulOrderMin`/`LawfulOrderMax` and the two left-leaning variants
(`Init/Data/Order/Classes.lean:54-190`). There is **no** top/bottom class in `Std`, so `never` as
the least element and `unknown` as the greatest stay plain theorems — `CTy.never_le` already is
one (`TypeAlgebra.lean:867`). Nothing in §4 needs a class that does not exist.

### 2.6 Cost and risk

The risk is concentrated and nameable. First, `sub`'s equations change shape, so the eleven
`sub_*_of_ne` lemmas (`Ty.lean:752-806`) that every proof rewrites with are replaced by two —
`sub_view` and `sub_union_*` — and the 35 unfold sites must be revisited in one pass. That is a
single mechanical commit, but it is not small, and it touches `Typed.lean`, which sits *below*
`Laws`, so it is in the core build. Second, `Ty.view` adds a definition that must agree with
`Ty`'s constructors, and nothing but the compiler's exhaustiveness check enforces that agreement
— the mitigation is to generate `view` and `variance` from the declaration in the `Fold` group,
beside `TyAlgebra`, so they cannot drift (the generator already reads constructor declarations
for the lenses and the binder table, manifest groups `NodeLenses` and `Binders`). Third, the
payoff is realised only if the same view is threaded into `hasTy`, which is the module the
straight soundness proofs consume. I would **not** do this inside the current push: it is the
right shape for the wave that lands row 2, where a new constructor family arrives and the
sixteen-fold boilerplate would otherwise be paid again.

---

## 3. Templates and inference

### 3.1 What the tree does now

`Ty.Subst` is an association list; `instantiate` substitutes with `never` for an unbound
parameter (`Ty.lean:451-475`); `infer` walks template and request in lockstep and binds each
variable **at its first occurrence** (`:482-493`); `matchTemplate` keeps the bindings only if
`sub request (instantiate σ' template)` (`:499-501`). `rowTy` normalises both sides and
instantiates the answer and error columns (`Typing/Rules.lean:114-117`), and the checker's
`perform` arm is three lines over it (`Checker.lean:131-137`). The one law is the guard:
`matchTemplate_sound` (`Laws/Program/Template.lean:54-57`).

### 3.2 What TypeScript actually does — and one correction to the plan

Read from `typescript.js` 5.9.2:

- inference keeps **two** candidate sets per type parameter, `candidates` and `contraCandidates`
  (`:73750-73761`);
- the covariant answer is `getCommonSupertype(baseCandidates)`, or the *subtype-reduced union*
  `getUnionType(baseCandidates, UnionReduction.Subtype)` when the priority flags imply
  combination (`:73742-73749`);
- the contravariant answer is `getCommonSubtype`, or an intersection under the same flag
  (`:73739-73741`);
- when both exist, the covariant one is preferred only if it is assignable to every
  contravariant candidate (`:73759`);
- and **when a parameter has no candidate and no default, the inferred type is `unknown`**, not
  `never`: `getDefaultTypeArgumentType` returns `unknownType` outside JavaScript
  (`:73785-73787`). `silentNeverType` appears only under the `NoDefault` inference flag
  (`:73763`).

So the plan's §2b(2) parenthetical — "A parameter the request leaves unbound is `never` — what
TypeScript infers for a parameter the arguments do not constrain" — is **wrong about
TypeScript**. The tree's choice is nonetheless the safe one, and for a reason worth writing
down rather than the one given: `never` is the bottom, so instantiating an unbound parameter at
`never` makes the instantiated template *smaller*, which makes the guard `sub request
(instantiate σ template)` *harder*. The choice can only refuse more, never admit more. TS's
`unknown` is the top, which would make the guard easier and would be the unsound direction here.
Recommendation: keep `never`, fix the justification, and add the side condition of §3.5 so that
the case cannot arise at all.

### 3.3 What the research says the right algorithm is

Three families, and for this language they collapse.

**Hindley–Milner unification** is the wrong tool: it solves equations, and subtyping needs
inequations. Bind `var 0` against `lit "a"` by unification and the row is instantiated at
`lit "a"` where it wanted `string`; the guard then rejects a request the row should accept.

**Subtype constraint solving** (Mitchell 1984; Fuh–Mishra 1988/1990; Aiken–Wimmers 1993;
Pottier 1996/1998; Dolan–Mycroft's MLsub 2017) is the right *theory*: collect inequations
`X ≥ τ` and `X ≤ τ` from the two sides, then solve. The general problem is hard because the
constraint graph cycles through function arrows and because simplification needs
polarity-indexed variables. This language has **no function types** (`language-cut.md` §2), so
no cycle exists, and the solved form is exactly a join of atoms.

**Local type inference** (Pierce–Turner 1998/2000; Odersky–Zenger–Zenger 2001; and the modern
framing in Dunfield–Krishnaswami's bidirectional-typing survey) is the right *shape*: infer type
arguments at the call site from the argument types and the expected type, with no global
constraint store. That is exactly what `rowTy` is — a call site with an argument type (the
request) and a fixed signature (the row) — and Pierce–Turner's own answer for a covariant
parameter is the join of the candidate lower bounds, which is `Ty.join`, whose least-upper-bound
property is proved here (`CTy.instLawfulOrderSup` via `sub_join_iff`, `TypeAlgebra.lean:863-864`).

### 3.4 The algorithm to write, and the completeness theorem to prove

Replace first-occurrence binding with constraint collection by variance. The tables of §2 give
the variance; the solver is fifteen lines.

```lean
inductive Constraint | lower (index : Nat) (bound : Ty) | upper (index : Nat) (bound : Ty)
                     | exact (index : Nat) (value : Ty)

/-- Collect, by variance: a covariant position gives a lower bound, a contravariant position an
    upper bound, an invariant position an equality. A union template with a variable inside is
    refused (§3.5), so there is no set-containment case. -/
def collect (v : Variance) : Ty → Ty → Option (List Constraint)
  | .var i, r => some [match v with
      | .co => .lower i r | .contra => .upper i r | .inv => .exact i r]
  | t, r => do
    let (ht, xs) ← t.view; let (hr, ys) ← r.view
    if ht == hr then
      (List.zip3 ht.variance xs ys).flatMapM fun (v', x, y) => collect (v.compose v') x y
    else some []          -- no correspondence: nothing inferred, the guard decides

/-- Solve: an equality pins, otherwise the join of the lower bounds, then every upper bound
    checked. `never` for an unconstrained variable (§3.2). -/
def solve (cs : List Constraint) (vars : List Nat) : Option Subst
```

with the guard unchanged, so `matchTemplate_sound` survives verbatim. The completeness theorem
this admits is the one that matters, and the lemma it needs **already exists**:

```lean
/-- A template variable is *anchored* when it occurs at an invariant position. -/
def anchored (t : Ty) (i : Nat) : Bool

theorem matchTemplate_complete_of_anchored (t r : Ty) (τ : Subst)
    (hvars : ∀ i ∈ t.vars, anchored t i = true)
    (hnormal : Normal r) (hτnormal : ∀ i x, τ.lookup i = some x → Normal x)
    (hτ : sub r (instantiate τ t) = true) :
    ∃ σ, matchTemplate [] t r = some σ ∧ ∀ i ∈ t.vars, σ.lookup i = τ.lookup i
```

The proof is induction on `t`; at an invariant position the two `sub` directions plus
`sub_antisymm_normal` (`TypeAlgebra.lean:499-570`) force `σ.lookup i = τ.lookup i`. **That is the
whole trick**: invariance turns inference into an equation, and the tree has already proved the
antisymmetry an equation needs. For a variable with only covariant occurrences the theorem
weakens to minimality — `σ`'s binding is below `τ`'s, pointwise — which is the standard
Pierce–Turner statement and which needs `sub_join_iff`, also proved.

This is not academic. The `Ref` rows of L4 make the anchored case the normal case:
`Ref.setAndGet` has request `prod refTy nat` (`src/Effect4/Program/Native.lean:131-132`), which
as a template is `prod (refOf (var 0)) (var 0)` — one invariant occurrence inside `refOf` and one
covariant occurrence as the written value. First-occurrence binding gets this right today only
because a row happens to spell the handle before the value, which the plan states as the reason
(§2b(2), "a row spells the handle before the value it writes"). Anchoring replaces that
dependence on spelling order with a property of the template.

### 3.5 Two side conditions, both decidable, both provable over the closed row table

**(a) Variables under a union are refused.** `infer`'s union arm matches positionally
(`Ty.lean:493`), and unions are canonical sorted antichains, so position carries no information:
template `union (var 0) string` against request `union nat string` binds `var 0 ↦ string` after
normalisation sorts `string` (key `[4]`) before `var 0` (key `[18,0]`), and the guard then fails
although `var 0 ↦ nat` would have succeeded. Matching a variable inside a union is the
set-containment problem `X ∪ string ⊇ nat ∪ string`, which is the genuinely hard case (it is what
set-theoretic type inference is for). Refuse it:

```lean
def Ty.templateAdmissible : Ty → Bool   -- no `var` below a `union` head
theorem rowTable_templateAdmissible : ∀ op : NativeOp,
    (NativeOp.row op).request.templateAdmissible = true   -- by `decide`, the alphabet is closed
```

**(b) Every variable of the answer and error columns is bound by the request or by the
operation.** This is the condition the plan satisfies by convention — "a row whose variables the
request does not fix carries them on the operation: `NativeOp.deferredMake (value error : Ty)`"
(§1) — and it should be a theorem, because the failure mode is silent: an unbound answer
variable instantiates to `never`, `hasTy v never = false` (`Typed.lean:94`), and
`Progress.answer_typed` becomes unprovable for that row rather than refusing at the boundary.

```lean
def Row.wellScoped (row : Row) : Bool :=
  (row.answer.vars ++ row.error.vars).all (row.request.vars.contains ·)
theorem nativeSignature_wellScoped : ∀ op : NativeOp,
    (nativeSignature.rowOf op).wellScoped = true            -- by `decide`
```

Both are `decide` over a finite alphabet and both sit beside `NativeOp.row_closed`
(`Laws/Program/Template.lean:87-92`), which is the same shape of theorem and is already proved.

### 3.6 One free improvement to the guard

The guard compares a **normal** request against a **possibly non-normal** instantiated template:
`rowTy` normalises `row.request` before matching and normalises the columns after instantiating,
but `matchTemplate`'s own `sub request (instantiate σ' template)` normalises neither
(`Ty.lean:499-501`, `Typing/Rules.lean:114-117`). Substituting a union into a `prod` argument
breaks `Normal`'s factor condition (`Ty.lean:583`), so the comparison is outside the order's
antisymmetric domain. Since `sub_normalize_of_sub` (`TypeAlgebra.lean:825-826`) carries the
relation forward through normalisation and the request is already normal, normalising the
template in the guard is **weaker** — it admits strictly more — so it cannot break soundness and
recovers completeness in exactly the union-substitution case. One character of change,
`(instantiate σ' template).normalize`, and one reference to an existing theorem.

### 3.7 Cost and risk

`collect`/`solve` replaces `infer`, so `infer_closed` (the 400-case split the plan notes) is
replaced by `collect_closed`, which is a one-liner over the view. The risk is the opposite of the
usual one: this design makes the checker admit programs it refuses today (more complete), so the
corpus's typing verdicts can change from refusal to admission — which is a golden-file change on
the `.ty` verdicts and must be reviewed row by row, not accepted wholesale. The mitigation is
that no row is a template yet (`NativeOp.row_closed`), so the change is inert until L4, and on
closed rows `matchTemplate_closed` (`Template.lean:60-62`) pins it to today's behaviour exactly.

---

## 4. A top type `unknown`, beside `never`

### 4.1 It landed while this note was being written; here is the review

Row 46's `Ty.unknown` is at HEAD as of this seat's last read. Read arm by arm, with the two
things that are **not** done marked:

| reader | what landed | note |
| --- | --- | --- |
| the inductive | constructor 2, with a docstring naming row 46 and `Effect.ts:12930` | `Ty.lean:25-28` |
| `sub` | `\| _, .unknown => true`, placed after the three lattice arms | `Ty.lean:427-428`; correct as placed, because a union on the left reaches the conjunction arm first and `sub a unknown && sub b unknown` is still `true`. Under §2's design this becomes one row of `Head.base` rather than a fourth lattice arm — see §2.3 for why `unknown` may be a head and `never` may not |
| `sub_unknown` | `theorem sub_unknown (t : Ty) : sub t unknown = true`, by induction with one union case | `Ty.lean:706-710` — the top edge as a law, not only as a definition |
| `normalize` / `Normal` | identity arm and a `Normal.unknown` constructor | `Ty.lean:561`, `:573`, `:620` |
| `key` | `[19]`, matching wire tag 19 | `Ty.lean:132`; `wire-tags.json` `Effect4.Program.Ty.unknown = 19`, append-only as the file's rules require |
| `members` / `isMember` / `isNever` / `closed` | `[.unknown]` / `true` / `false` / `true` | `Ty.lean:106`, `:392`, `:176`, `:186` — `isMember = true` is what makes §4.2 work |
| `renderRaw` / `ofNormalized` | `"unknown"` / `.name ["unknown"] []` | `Ty.lean:81`, `Codegen/Types.lean:270`; `"unknown"` was already a reserved keyword of the legacy parser (`:158`) |
| `schema` / `ofSchema` | `Representation.unknown` both ways, `ofSchema_schema` by `rfl` | `Schema/Bridge.lean:40`, `:81`, `:143` — the persisted carrier already had the node (`Schema/Representation.lean:721`), so this cost one line each |
| `Val.hasTy` | `true` for every value | `Typed.lean:95` |
| `hasTy_sub` | a `by_cases b = .unknown` at the top, then the sixteenth union block | `Typed.lean:147-168` |
| `rawSupportedErrTy` | `false` | `Eff.lean:62` — exactly right: it keeps `fail`/`failCause` from introducing `unknown` while leaving `exitOf a unknown` typable, because the exit arm of `hasTy` goes through `causeAdmits` and not through `supportedErrTy` (`Typed.lean:69-80`) |
| `findInt` | `none` | `Admission.lean:41` |
| row 47 | the release's exit parameter is now `exitOf .unknown .unknown` and the children snapshot is `list (fiberOf .unknown .unknown)`, compared by `Ty.sub` rather than by equality | `Checker.lean:203-206`, `:366-369` — the placeholder `handle "unknown"` is gone |
| `Codec.isSupported` | **not touched** — `unknown` falls through `\| _ => true` | `Schema/Codec.lean:45-49`; see §7.3, this is now the fourth constructor in that position |
| absorption / the top of `CTy` | **not stated** — `CTy.unknown` exists (`Ty.lean:838`) but there is no `join_unknown` and no `CTy` counterpart of `never_le` | §4.2; one line each |

### 4.2 Absorption comes from the antichain, not from a new rule

`normalize` sends a union through `normalizeRow`, which is `Row.antichain sub` over the sorted
members (`Ty.lean:530-532` before the landing; the definition is unchanged), and `antichain` keeps
exactly the members with no strict dominator (`Data/Row.lean:277`, `mem_antichain_iff` at `:291`).
With `sub m unknown = true` for every `m` (now a theorem, `sub_unknown`) and `sub unknown m =
false` for every other member, `unknown` dominates, so `normalize (union t unknown) = unknown`
**by the existing filter**. No absorption case was needed and none was written; that is why the
landing only had to add `exact .unknown` to `normal_normalize` (`Ty.lean:620`).

What is still owed is saying so. Two theorems, each a few lines, and both worth having because
they are what a reader of the type algebra will look for:

```lean
theorem join_unknown (t : Ty) : join t unknown = unknown       -- via mem_normalizeRow + sub_unknown
theorem CTy.le_unknown (t : CTy) : t ≤ unknown := Ty.sub_unknown t.toRaw
```

`CTy.le_unknown` is the mirror of `CTy.never_le` (`TypeAlgebra.lean:867`); `Std` has no
`OrderTop` class (§2.5), so both stay plain theorems rather than instances.

### 4.3 The one real hazard: `hasTy v unknown = true` and the erased-handle story

`hasTy v unknown = true` for **every** value, including a handle. That is sound as a typing
(`hasTy_sub` at `b = unknown` is immediate) and it is what rc.112 means by `Exit<unknown,
unknown>` (`Effect.ts:12930`, per decisions row 47). But it makes `unknown` a type at which a
*handle* can be stored and later read back, and the world-table story of row 44 types a handle
by its kind, not by its static type. Two consequences to state:

1. `Codec.isSupported` must get an explicit `false` arm and did not
   (`Schema/Codec.lean:45-49`): a boundary that consults it now claims `unknown` is encodable,
   while `encodeRaw`'s `| _, _ => none` refuses every value at it (`:171`). Nothing consults it
   today, so this is a dormant false claim, and it is the fourth constructor to land in that
   position — see §7.3.
2. A release body's exit parameter at `exitOf unknown unknown` (row 47, landed at
   `Checker.lean:203-206`) means the release can observe an exit it cannot decode. That is
   correct against rc.112 and it is the reason row 47 also requires the release's error column to
   be `never`: the release may look at the exit, and may not fail on what it finds.
3. `unknown` is now a legal *answer* type, so `Ty.join answer unknown = unknown` will appear in a
   branch join as soon as one arm answers `unknown`, and every downstream `hasTy` obligation at
   that answer becomes trivially true. That is sound and it is a real loss of information: a
   program whose answer type is `unknown` has an answer nothing can read. Worth a register row
   rather than a refusal, because rc.112 does the same.

### 4.4 What the landing cost, and what to watch

Measured against the tree as read: fifteen arms and one wire tag, no proof restructured, no new
constructor in any generated algebra field beyond the mechanical one, absorption free. The two
loose ends are the classifier default (§7.3) and the two unstated theorems (§4.2). Both are
small; neither blocks L6.

---

## 5. Canonical forms: sorted antichains, distributed products

### 5.1 What the tree does, and what TypeScript does

`normalize` (`Ty.lean:547-567`): recurse into every argument; a union becomes its members' union,
sorted by the injective structural key, deduplicated, filtered to the maximal members
(`normalizeRow`); a product distributes over its factors (`productMembers`, `:543-544`) and the
resulting member list is normalised the same way. `Normal` is the erased invariant (`:571-594`),
`normalize_idem` is proved (`:692-693`), and the public carrier `CTy` is the subtype
(`:812-818`).

TypeScript, read on disk, does four of those five things and makes the fifth optional:

| step | tree | TypeScript 5.9.2 |
| --- | --- | --- |
| flatten nested unions | `members` (`Ty.lean:104-124`) | `addTypesToUnion` recurses into `Union` (`typescript.js:65845-65854`) |
| drop the empty type | `members .never = []` | `addTypeToUnion` skips `Never` (`:65827`) |
| sort and dedup | by `key`, with `insertMember` (`:130-165`) | by interned `type.id`, binary search (`:65837-65840`) |
| absorb literals into their base | falls out of `antichain sub` (`lit s ≤ string`) | a dedicated cheap pass, `removeRedundantLiteralTypes` (`:65909-65920`) |
| remove non-maximal members | **always**, `antichain sub` | **only on request** (`UnionReduction.Subtype`), with a cache, a 10⁵/10⁶ work cap and a hard error "union type that is too complex to represent" (`removeSubtypes`, `:65855-65908`); the default is `UnionReduction.Literal` (`getUnionType`, `:65992`) |

So the design is the mainstream one, with one deliberate difference: the tree pays full subtype
reduction unconditionally. `antichain` is `xs.filter fun x => xs.all fun y => !le x y || le y x`
(`Data/Row.lean:277`) — quadratically many `sub` calls, each itself recursive — and normalisation
is called on every row's columns, on every `join`, and inside `Decision.arms`
(`Decision.lean:64-73`). For the sizes this language sees (error columns of a handful of tagged
pairs) that is the right trade: canonical forms make `key` a type identity, which is what the
wire, the row sort and `CTy`'s antisymmetry all rest on. It is worth recording the cap TypeScript
found necessary, because the corpus generator at scale is where it would show up
(`docs/research/2026-09-16-testing-corpus-coverage.md` reports 10× scale not helping coverage;
it would be the place to notice this cost).

### 5.2 Where it breaks, precisely

Three gaps, all in the same direction — the order is **sound but not complete** for value
containment — and the tree half-says so: "One-way preservation of the raw relation by
normalization. No converse is asserted" (`TypeAlgebra.lean:824`).

1. **`option` and `list` of a union.** `normalize` recurses into the argument but never
   distributes out of it, and `sub` relates the two forms in one direction only.
   `sub (option nat) (option (nat | string)) = true`; `sub (option (nat | string)) (option nat |
   option string) = false`, because the right-hand rule is a choice per member and neither member
   covers the whole. Yet the two types have **exactly the same inhabitants**: unfolding
   `Val.hasTy` at `.option` (`Typed.lean:41-45`) and at `.union` (`:92`) gives
   `hasTy (some x) (option (a|b)) = hasTy x a || hasTy x b = hasTy (some x) (option a) ||
   hasTy (some x) (option b)`, and `none` inhabits all of them. So the checker refuses a request
   it should accept. Incompleteness, not unsoundness.
2. **Product annihilation.** `factors .never = [.never]` keeps an explicit `never` factor, with
   the comment saying so on purpose (`Ty.lean:503-504`). So `prod never nat` is a canonical form
   with no inhabitants (`hasTy` needs both components, `Typed.lean:81-84`) that is not equal to
   `never` and is not below it. Same direction.
3. **Function types are absent**, so the hardest case of union normalisation — distributing an
   arrow over a union in its domain — does not arise, and no contravariant position exists
   anywhere in the language. This is why §3's solver never needs a meet, and it is the single
   biggest simplification the profile buys.

### 5.3 What the alternatives would give, and whether to want them

**Set-theoretic / semantic subtyping** (Frisch–Castagna–Benzaken, JACM 2008; CDuce;
Castagna–Xu ICFP 2011) closes all three gaps by *defining* `s ≤ t` as containment of value sets,
decided by emptiness of `s ∧ ¬t` over a DNF with unions, intersections and negations. It is the
only approach that makes the order complete for the inhabitant semantics, and it is what one
would reach for if `option (a|b)` versus `option a | option b` ever mattered. The price is an
intersection and a negation constructor, a DNF normal form instead of a sorted antichain, and a
decision procedure that is exponential in the worst case — three things this estate has ruled
against for the stored program.

**Flow's approach** — subtyping by constraint propagation over a type graph with speculative
selection of union branches, no canonical form at all — is the opposite trade and would give up
`key` as a type identity, which the wire depends on.

Recommendation: **keep the antichain, and state the incompleteness as a named property rather
than leaving it implicit.** One theorem records the gap honestly and one counterexample pins it:

```lean
/-- `sub` is sound for value containment. -/
theorem sub_sound (a b : Ty) (h : sub a b = true) (v : Val) (allocated : List String) :
    Val.hasTy v a allocated = true → Val.hasTy v b allocated = true := hasTy_sub a b v allocated h

/-- and not complete: `option nat | option string` and `option (nat | string)` have the same
    inhabitants and are unrelated. -/
theorem sub_not_complete :
    (∀ v allocated, Val.hasTy v (.option (.union .nat .string)) allocated =
      Val.hasTy v (.union (.option .nat) (.option .string)) allocated) ∧
    sub (.option (.union .nat .string)) (.union (.option .nat) (.option .string)) = false
```

The second conjunct is `decide`; the first is a short `cases v` over four frames. That converts a
silent design gap into a register row, which is what the estate does with every other gap
(`E4-*-CE-*`).

---

## 6. What the LCNF / OCaml reification needs from `Ty`

### 6.1 The actual constraint chain

Three consumers read `Ty`'s *declaration*, not its meaning:

1. `Conform.Source.readShape` turns each constructor field into a `Shape`, which has exactly
   `nat bool string unit option list prod nominal canonicalRow` and throws on anything else —
   "unsupported field", and no function, dependent or free-variable field passes
   (`tools/Conform/Source/Description.lean:12-54`). `Ty` is a one-member block in the selection
   (`tools/Tools/ProgramStructure.lean:19`).
2. `OCaml5.Eff.projectShape` maps that `Shape` to an OCaml carrier `OTy`, which has `int bool
   string unit option list prod named requirements` (`src/OCaml5/Eff/World.lean:40-48`,
   `:105-119`); a `Shape` it cannot carry is a refusal, and the module's own claim is that the
   emitter throws rather than emitting a hole (`:20`).
3. `tyO` renders a `Ty` *value* as OCaml source, one arm per constructor
   (`src/OCaml5/Eff/Emit.lean:366-385`), and the wire tags fix the byte for each
   (`tools/Effect4Gen/wire-tags.json`, `Effect4.Program.Ty` active 0–19 after §4's landing).

And then LCNF: the translator lowers Lean functions over `Ty`, handling `cases` on an inductive
as a `match` with alternative patterns, `List`-shaped carriers through `carrierRewrite?`/
`useAsList`, and refusing six named shapes (`docs/core/lcnf-route.md` §2).

### 6.2 What each recommendation does to that chain

| recommendation | effect on the chain |
| --- | --- |
| §2 head/variance view | **none**. `Head`, `Variance`, `view` and `variance` are definitions *about* `Ty`, not fields of it. They only reach OCaml if a lowered function calls them, and then they are ordinary first-order Lean the translator already handles. `Head` would need a `ProgramStructure` entry only if it appears in a *stored* field, which it must not. |
| §3 `collect`/`solve` | **none** for the carrier; `Constraint` is transient. `Subst = List (Nat × Ty)` already projects (`Shape.list (Shape.prod .nat (.nominal Ty))` → `(int * ty) list`). Note that typing stays in Lean: "Program typing remains in Lean" (`Emit.lean:10`). |
| §4 `Ty.unknown` | one wire tag, one `tyO` arm, one OCaml constructor. Argument-less, so the cheapest possible addition. |
| §5 the incompleteness theorem | none. |
| §1 option B (mutual `Ty`/`Fields`) | `Fields` becomes a second member of the block: one `ProgramStructure` spec line beside `Ty`'s (the `Eff` group shows a seven-member block, `ProgramStructure.lean:37-42`), one OCaml type in the same `type … and …` group, wire tags for two constructors, and `fold_of`'s list-sibling shape. All supported. |
| §1 option C (nested `List Ty`) | also supported at the boundary — `Shape.list` exists, `OTy.list` exists, `ty list` renders — so the OCaml side is **not** the reason to refuse C. The reasons are F1, F3+F4 and the nine-fold proof fan-out of §0, plus the loss of the generated monadic half for a block with a composite position (manifest, SchemaFold group note; `TyMAlgebra` at `Fold.lean:327` has no consumer today, so this is a paper loss). |
| §1 option D (binary `app`) | supported, and the arity check moves into every consumer. |
| an indexed family (`Fin n → Ty`) | **refused by the chain**: a function field has no `Shape`. |

### 6.3 The rule to carry

`Ty` must stay a **first-order, non-dependent, proof-free inductive whose every field is a
`Shape`**. That is the invariant the reification depends on, and it is compatible with
everything recommended here. Two things would break it and are therefore off the table: a proof
field (a `Row Ty` or a `Subtype` inside the carrier — which is why `Normal` is erased and `CTy`
is a wrapper, `Ty.lean:6-9`, `:812`), and a function field. **This is the single sentence to put
in `Ty.lean`'s header**, because at present the header says why `Normal` is erased but not why the
carrier's shape is fixed by a consumer three packages away.

---

## 7. Recommendations for the push

### 7.1 Now, inside this push (L2–L7)

1. **Fix the `Ty.infer` justification and add the two side conditions of §3.5** —
   `templateAdmissible` (no variable under a union) and `Row.wellScoped` (every answer/error
   variable bound by the request or the operation), both by `decide` beside
   `NativeOp.row_closed` (`Laws/Program/Template.lean:87-92`). Cheap, and they are what makes
   the `never`-for-unbound choice provably unreachable rather than conventionally safe.
2. **Normalise the instantiated template in the guard** (§3.6). One character; strictly more
   complete; justified by `sub_normalize_of_sub`, which is proved.
3. **Finish `Ty.unknown`** (§4), which landed during this seat: add `join_unknown` and
   `CTy.le_unknown` (two theorems, §4.2) so the top is stated and not only defined.
4. **Correct `Codec.isSupported`'s classification of `refOf`, `deferredOf`, `var` and now
   `unknown`** — four constructors have defaulted into "supported" through its wildcard; see
   §7.3, and take the general rule with it: wildcards belong in proofs, never in classifiers.
5. **Put the carrier rule of §6.3 in `Ty.lean`'s header.**

### 7.2 After the push, in the wave that lands row 2

6. **The head/variance view and the generic `sub`/`hasTy_sub` proofs** (§2), generated from the
   declaration in the `Fold` group so `view` and `variance` cannot drift from `Ty`. Do it *with*
   row 2, when a constructor family arrives and the sixteen-fold boilerplate would be paid again;
   the plan already says row 2 "needs a ruling … Recommended after this push, as its own plan".
7. **Records and variants as a mutual `Fields` spine** (§1.3), not `List (String × Ty)` and not
   `Ty.app`. Row 3's `Ty.app` is superseded by `Ty.foreign (id) (args : Fields)` — an opaque
   nominal type, invariant and uninhabited — which is what row 1 actually needs and which keeps
   every law of §2 true.
8. **`collect`/`solve` with the anchored-completeness theorem** (§3.4), once a row has a variable
   at more than one position. `Ref.setAndGet` is that row, so this is due at L4 if L4's rows are
   to be more than sound.
9. **The incompleteness register row of §5.3**, so the `option (a|b)` gap is written down.

### 7.3 Findings to hand back

- **`Codec.isSupported` now misclassifies four constructors.** It reads
  `| .handle _ | .fiberOf _ _ | .int => false` … `| _ => true` (`src/Effect4/Schema/Codec.lean:45-49`),
  so `refOf`, `deferredOf`, `var` and — since this evening — `unknown` all fall through to
  `true`. Before step 1 a cell was `handle "Ref.Ref<number>"` and answered `false`; it now answers
  `true`, while `encodeRaw` still refuses every value at all four via `| _, _ => none` (`:171`).
  Nothing consumes `isSupported` today — the only references are the `fold_of` registration
  (`Program/Folds/Ty.lean:36`) and the abbrev `isCodecSupported` (`Codec.lean:244`) — so this is a
  dormant false claim, not a broken theorem. The general lesson is the counterweight to the
  owner's wildcard rule: a wildcard is right in a **proof** (a new constructor must not touch
  one) and wrong in a **classifier**, where it makes a new constructor default into the positive
  class silently. The repair is cheap and mechanical: a classifier lists its positive arms
  exhaustively and closes with an explicit `false`, so the compiler's exhaustiveness check stops
  being bypassed; the census is the instrument that can tell the two kinds apart, since
  `#traversal_census Effect4.Program.Ty` already names every `Ty` reader and `Codec.isSupported`
  is one of the sixteen folds (`Program/Folds/Ty.lean:36`). Two landings in one day have now put
  four constructors on the wrong side of this one predicate — a second occurrence, which by the
  owner's own instrument rule is when the instrument gets built rather than the arm patched.
- **The plan's TypeScript claim in §2b(2) is wrong** and the correct justification is better
  (§3.2). TypeScript infers `unknown` for an unconstrained parameter
  (`getDefaultTypeArgumentType`, `typescript.js:73785-73787`); `never` appears only under the
  `NoDefault` flag. `never` is nonetheless the right choice here because it can only make the
  guard harder.
- **`infer`'s union arm is positional** (`Ty.lean:493`) and therefore arbitrary against a
  canonical request; no row exercises it yet. §3.5(a) refuses the case rather than fixing it.
- **`sub` is checked against a non-normal instantiated template** (§3.6), which is outside the
  domain where `sub_antisymm_normal` holds.
- **The plan's "nested loses every `induction`" is stronger than the truth.** Structural
  recursion through a nested container works (F5, F6, and `Schema/Fold.lean:128-171` relies on
  it); what is lost is derived equality (F1), a non-`partial` derived `Repr` (F3+F4) and the
  `induction` tactic's automatic hypotheses — the last measured in-tree at nine functions plus
  nine theorems for one property (`Schema/Representation.lean:812-1067`). The conclusion (use
  dedicated constructors now) is unchanged; the reason for row 2 changes, because a mutual spine
  sibling pays only the `Repr` bill.

---

## 8. References

**The tree (read at the cited lines; `Ty.lean`, `TypeAlgebra.lean` and `Typed.lean` are cited at
their line numbers *after* the `Ty.unknown` landing of §4, which moved everything below the
inductive by five lines).** `src/Effect4/Program/Ty.lean` — the inductive `:23-59` (`unknown`
`:25-28`), `renderRaw` `:79-101`, `members` `:104-124`, `key` `:130-150`, `isNever` `:174-179`,
`closed` `:184-189`, `key_injective` `:237-260`, the `Std` order instances `:373-384`, `isMember`
`:387-392`, `sub` `:421-440` (the top arm `:427-428`), the template calculus `:451-501`, `factors`
`:505-508`, `normalizeRow` `:530-532`, `productMembers` `:543-544`, `normalize` `:547-567`,
`Normal` `:571-594`, `normal_normalize` `:617-653`, `normalize_idem` `:692-693`, `join` `:704`,
`sub_unknown` `:706-710`, the tag algebra `:714-747`, the `sub_*_of_ne` lemmas `:752-806`, `CTy`
`:812-852` (`CTy.unknown` `:838`). `src/Effect4/Laws/Program/TypeAlgebra.lean` — `sub_trans_core`
`:10-71` (invariant alternatives `:34-38`; the `unknown` short-circuit `:14-15`),
`hasTy_normalize` `:183-223`, the join laws `:317-362`, `sub_antisymm_normal` `:499-570`
(`:522-528`), `sub_normalize_of_sub` `:749-801` (`:774-777`), its one-way note `:824-826`, the
`CTy`/`ErrTy` order instances `:854-913` (`instLawfulOrderSup` `:863-864`, `never_le` `:867`).
`src/Effect4/Program/Typed.lean` — `Val.hasTy` `:34-101` (`never` `:94`, `unknown` `:95`), the
monotonicity helpers `:115-141`, `hasTy_sub` `:144-399` (the top short-circuit `:147-148`).
`src/Effect4/Laws/Program/Template.lean` — `matchTemplate_sound` `:54-57`, `matchTemplate_closed`
`:60-62`, `rowTy_closed` `:67-84`, `NativeOp.row_closed` `:87-105`.
`src/Effect4/Program/Typing/Rules.lean` — `EffTy` `:26-45`, `Signature` `:49-66`, the term typer
`:77-107`, `rowTy` `:114-117`, `catchIfError` `:217-222`. `src/Effect4/Program/Checker.lean` —
`perform` `:131-137`, `iterate` `:178-189`, the `unknown` placeholder `:361`, `:364`.
`src/Effect4/Program/Eff.lean` — `rawSupportedErrTy` `:56-68`, `Row` `:192-215`, the `Eff` mutual
block and its derived equality `:265-419`. `src/Effect4/Program/Decision.lean` — `arms` `:64-73`.
`src/Effect4/Program/Fold.lean` — `TyFam`/`TyAlgebra`/`cata_ty`/`TyHom` `:27-123`, `TyMAlgebra` `:327`.
`src/Effect4/Program/Folds/Ty.lean` `:23-38`. `src/Effect4/Program/FoldOf.lean` `:1-50` (the five
shapes `fold_of` knows). `src/Effect4/Data/Row.lean` — `Row` `:30-33`, `antichain` `:277`,
`mem_antichain_iff` `:291`, `antichain_coverage` `:342`. `src/Effect4/Schema/Bridge.lean` —
`schema` `:38-58`, `ofSchema` `:78-137`, `ofSchema_schema` `:138`, `:263`.
`src/Effect4/Schema/Codec.lean` — `layout` `:26-34`, `isSupported` `:45-49`, `encodeRaw`
`:147-171`. `src/Effect4/Schema/Representation.lean` — the mutual nested carrier `:701-780`, the
"no handler for a mutual nested inductive" note `:797-806`, the hand equality `:812-1067`.
`src/Effect4/Schema/Fold.lean` — the generated nested algebra `:20-44`, `cata_representation`
`:128-171`. `src/Effect4/Codegen/Types.lean` — the non-injectivity note `:23-25`, `ofNormalized`
`:268-313`, `ofTy` `:321`. `src/Effect4/Program/Native.lean` — the `Ref`/`Deferred` rows
`:130-175`. `src/Effect4/Program/Admission.lean` — `findInt` `:31-41`.
`tools/Conform/Source/Description.lean` — `Shape` `:12-19`, `readShape` `:35-54`.
`tools/Tools/ProgramStructure.lean` — the selection `:18-51`. `src/OCaml5/Eff/World.lean` — `OTy`
`:40-48`, `projectShape` `:105-119`. `src/OCaml5/Eff/Emit.lean` — `tyO` `:366-385`, "Program
typing remains in Lean" `:10`. `tools/Effect4Gen/wire-tags.json` — the `Ty` assignment.
`tools/Effect4Gen/manifest.json` — the `Fold`, `SchemaFold`, `NodeLenses`, `Binders` groups.
`scripts/test-trust-gate.sh` `:3`, `:302` — the `partial` refusal. `docs/core/lcnf-route.md`,
`docs/core/traversal-census.md` §3.2 and §7.4, `docs/core/language-cut.md`,
`docs/core/decisions.md` rows 2, 3, 42–47, 55, `docs/research/2026-09-18-rows-42-43-plan.md`.

**Lean 4.33.1 (read at `~/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean`).**
`Lean/Elab/Deriving/DecEq.lean:180-199`, `:211-212` — why a nested inductive has no derived
decidable equality and how a mutual one gets it. `Lean/Elab/Deriving/Repr.lean:98-105` with
`Lean/Elab/Deriving/Util.lean:116` — why `Repr` goes `partial` for nested *and* mutual blocks.
`Lean/Data/Json/Basic.lean:180-191` — Lean's own nested `Json` with a `partial` equality: the
canonical precedent. `Init/Data/List/BasicAux.lean:230-246` — `List.sizeOf_lt_of_mem` and the
`decreasing_trivial` extension whose docstring names the nested-list recursion pattern.
`Init/Data/Order/Classes.lean:54-190` — every `Std` order class available here, and the absence
of a top/bottom class.

**TypeScript 5.9.2 (read at `ts/eff/node_modules/typescript/lib/typescript.js`).**
`:65825-65854` `addTypeToUnion`/`addTypesToUnion` — flatten, drop `never`, insert into an
id-sorted set. `:65855-65908` `removeSubtypes` — optional subtype reduction with a cache and a
work cap. `:65909-65920` `removeRedundantLiteralTypes` — literal absorption as a cheap pass.
`:65992-66018` `getUnionType` — default reduction is `Literal`, not `Subtype`.
`:73739-73749` `getContravariantInference`/`getCovariantInference` — meet versus join per
variance. `:73750-73784` `getInferredType` — two candidate sets and the covariant preference
rule. `:73785-73787` `getDefaultTypeArgumentType` — an unconstrained parameter infers `unknown`.

**Literature (assumed; not read here).**
*Inference with subtyping.* J. Mitchell, "Coercion and type inference" (POPL 1984). Y.-C. Fuh and
P. Mishra, "Type inference with subtypes" (ESOP 1988; TCS 1990). A. Aiken and E. Wimmers, "Type
inclusion constraints and type inference" (FPCA 1993). F. Pottier, "Simplifying subtyping
constraints" (ICFP 1996) and "Type inference in the presence of subtyping: from theory to
practice" (INRIA RR-3483, 1998). S. Dolan and A. Mycroft, "Polymorphism, subtyping, and type
inference in MLsub" (POPL 2017); S. Dolan, *Algebraic Subtyping* (thesis, 2017) — why polarity,
not first-occurrence, is the principled way to bind a variable that occurs in both positions.
*Local inference.* B. Pierce and D. Turner, "Local type inference" (POPL 1998; TOPLAS 2000) —
the algorithm `rowTy` is an instance of. M. Odersky, C. Zenger, M. Zenger, "Colored local type
inference" (POPL 2001). J. Dunfield and N. Krishnaswami, "Bidirectional typing" (ACM CSUR 2021)
— the frame for annotations like `iterate`'s cursor type.
*Set-theoretic types.* A. Frisch, G. Castagna, V. Benzaken, "Semantic subtyping: dealing
set-theoretically with function, union, intersection, and negation types" (JACM 2008);
G. Castagna and Z. Xu, "Set-theoretic foundation of parametric polymorphism and subtyping"
(ICFP 2011) — the only approach that makes §5.2's gaps disappear, at the cost of intersection,
negation and an exponential decision procedure.
*F-sub and why not.* B. Pierce, "Bounded quantification is undecidable" (POPL 1992);
L. Cardelli, S. Martini, J. Mitchell, A. Scedrov, "An extension of System F with subtyping"
(1994); B. Aydemir et al., "Mechanized metatheory for the masses: the POPLmark challenge"
(TPHOLs 2005) — the standard reference point for formalising a subtyping relation, and the
reason a first-order table beats bounded quantification here.
*Records and rows.* M. Wand, "Type inference for record concatenation and multiple inheritance"
(LICS 1989). D. Rémy, "Type inference for records in a natural extension of ML" (1994).
B. Gaster and M. Jones, "A polymorphic type system for extensible records and variants" (1996).
D. Leijen, "Extensible records with scoped labels" (TFP 2005). J. G. Morris and J. McKinna,
"Abstracting extensible data types" (POPL 2019) — row theories, if `Ty.record` ever needs row
polymorphism rather than a closed field list.
*Variance as declaration.* B. Emir, A. Kennedy, C. Russo, D. Yu, "Variance and generalized
constraints for C# generics" (ECOOP 2006) — declaration-site variance checked once, the model
§2's table follows. rc.112's own declarations are the data (`Fiber.ts:70`, `Ref.ts:59`,
`Deferred.ts:58`, per decisions row 55).
*Generic proofs over a description.* M. Benke, P. Dybjer, P. Jansson, "Universes for generic
programs and proofs in dependent type theory" (2003); J. Chapman, P.-É. Dagand, C. McBride,
P. Morris, "The gentle art of levitation" (ICFP 2010); T. Altenkirch, N. Ghani, P. Hancock,
C. McBride, P. Morris, "Indexed containers" (JFP 2015) — the literature behind "declare the
signature, prove the laws once", which is what §2 does in miniature.
*Hash-consing.* J.-C. Filliâtre and S. Conchon, "Type-safe modular hash-consing" (ML 2006);
J. Goubault, "Implementing functional languages with fast equality, sets and maps" (1994) — the
technique LLVM, MLIR and TypeScript all use for type identity, and the reason `Ty.key` plus
`key_injective` is the estate's purely functional stand-in for it.
*Compiler infrastructure.* LLVM, *The LLVM Language Reference* (Type System: literal versus
identified struct types) and *The LLVM Target-Independent Code Generator* — the target-as-data
model the owner's 2026-09-17 steer names. C. Lattner et al., "MLIR: scaling compiler
infrastructure for domain specific computation" (CGO 2021) — uniqued type and attribute storage.
S. Ullrich and L. de Moura, "Counting immutable beans" (IFL 2019) and A. Reinking et al.,
"Perceus" (PLDI 2021) — the Lean pipeline below LCNF. J. Zhao et al., "Formalizing the LLVM
intermediate representation for verified program transformations" (POPL 2012, Vellvm);
N. Lopes et al., "Alive2" (PLDI 2021) — the low tier's own verification story.
