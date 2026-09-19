# The term language and its atom table (research, 2026-09-18)

A research seat's answer to six questions about `Term`, `NativeAtom` and the function-taking
rows about to land, each with a concrete Lean design, a sketch of the definitions, the proof
strategy, and an honest cost paragraph. Nothing here was compiled: this seat is read-only and
the main session holds the one compiler. Every claim about the tree is **read** at the cited
`file:line`; every claim about a design is **proposed** and says so. The two evidence words that
appear below mean what the project means by them: **proved** = a Lean theorem exists at the
citation; **tested** = a check or `#guard` exists; everything else is **assumed**.

## 0. The tree at this hour, because it moved while I read it

L1 of the language push (`docs/research/2026-09-18-rows-42-43-plan.md` §2c) landed during this
session. What it did, read at the files:

- `src/Effect4/Machine/Alphabets.lean` (new, 363 lines): `Err`, `Defect`, `Ann`, `CauseV`,
  `ExitV`, their images, and the machine's view of the carrier, moved out of
  `Machine/Stores.lean` so a store step can evaluate a term. `Err` is four constructors —
  `boom | tag (code) | tagged (tag message) | text (message)` (`Alphabets.lean:33-40`), not the
  two the cut's §3 first reported; the stale copy under `Machine.Env` is gone.
- `src/Effect4/Machine/Term.lean` (new): `Lit`, `Var`, `Term`, `Terms`, `Terms.toList`,
  `Term.scoped`/`Terms.scoped`, `Lit.toVal`, `Val.tuple`/`tuple?`, `stringsAtom`, the
  `NativeAtom` inductive with `all`/`all_complete`/`name`/`names`/`ofName?`/`arity`/`tagHit`/
  `eval`, `nativeAtom`, and `evalTerm`/`evalTerms`, all in namespace `Effect4.Program`.
- `src/Effect4/Program/NativeAtom.lean` is now the **typing half only**: `causeInputError?`,
  `constGeneric`, `mono`, `projectProduct`, `typeOf`, `typeOf_mono` (114 lines). It imports
  `Effect4.Program.Ty` and `Effect4.Machine.Term`.
- `Lit.ty` stayed in `Program/Eff.lean` (`:236-240`), because it needs `Ty`.

So the split the plan asked for is in place, and the shape of the atom inventory is now: **one
enum, two modules** — the inventory and its evaluation below the stores, its typing above them.
Everything in §1 below is designed against that split, not against HEAD.

## 1. The atom table as one declarative object

### 1.1 What the prior art actually gives us

Four instruction/intrinsic tables are worth naming, and they do not all teach the same lesson.

- **GHC's `primops.txt.pp`** is the closest analogue and the one to copy. One file declares each
  primop's name, its type (in a small type language with type variables and levity), its arity,
  strictness, whether it `has_side_effects`, `can_fail`, `commutable`, plus its documentation
  string; `genprimopcode` generates the `PrimOp` datatype, the name table, the type-of function,
  the fixity table and the user manual from it. The lesson: the table's *type* column is a small
  DSL, and everything downstream is a projection.
- **LLVM's `Intrinsics.td`** (TableGen) declares each intrinsic's signature over a type
  vocabulary (`llvm_i32_ty`, `LLVMMatchType<0>`) plus attribute sets; `llvm-tblgen` emits the
  enum, the name table, the signature verifier and the attribute tables. The lesson we want:
  `LLVMMatchType<0>` is exactly a *type variable bound at its first occurrence*, which is what
  we already have as `Ty.var` + `Ty.infer`.
- **Cranelift's meta DSL** (`cranelift/codegen/meta`) declares instruction formats and type
  variables in Python and emits Rust; the lesson is the negative one — a table in a *different
  language* from the compiler cannot be type-checked against it. We must not do that.
- **Lean's own** `Lean.Compiler.LCNF` has no single intrinsic table; the nearest thing is
  `@[extern]`/`@[implemented_by]` attributes plus `Lean.Compiler.LCNF.toLCNF`'s special cases,
  and our tree's analogue is `OCaml5.Lcnf.Translate.builtin?` (`src/OCaml5/Lcnf/Translate.lean:154-230`),
  a 50-row match from a Lean constant name to an OCaml expression former. That one *is* our
  precedent for "a table as a Lean function on a name", and it works.
- **WebAssembly's opcode table** in the spec is a flat list of opcode, name, signature; the
  lesson is that a *closed* opcode space plus a validation function in the same document is
  enough, no metaprogramming required.

The thing none of them does, and we can: put the table in the same language as the checker, so
the compiler's own exhaustiveness check is the completeness proof.

### 1.2 The design: one record, two forced dispatches, no function fields

The mistake to avoid is the obvious one — `structure AtomSpec where eval : List Val → Option Val`.
A function field would (a) kill `DecidableEq` on the table, (b) make the table's rows opaque to
`#guard`, and (c) put a closure in the LCNF lowering path where a `match` is today (§6). So the
record holds **only first-order data**, and the two semantic columns stay dispatches on the enum
that the compiler forces exhaustive.

```lean
namespace Effect4.Program.NativeAtom
-- Declaration order matters: `Scheme` (§2.1) comes before `Spec`, and both come after the
-- `NativeAtom` inductive. Lean has no forward references, which is the trap that bit
-- `Machine/Term.lean` an hour ago when `Lit.toVal` was written above `inductive Lit`.

/-- Where an atom's meaning comes from, for the faces. First-order data only. -/
structure Spec where
  /-- The wire and prelude name (`NativeAtom.name` today). -/
  name     : String
  /-- `some n` fixed arity, `none` variadic (`NativeAtom.arity` today). -/
  arity    : Option Nat
  /-- The typing scheme as data (§2). Replaces `mono` and most of `typeOf`. -/
  scheme   : Scheme
  /-- The literal rule's flag (`constGeneric` today, DI-55). -/
  constGen : Bool
  /-- The TypeScript prelude's one-line spelling, as text, so the prelude is generated. -/
  ts       : String
  /-- The OCaml spelling when the LCNF lowering needs a row; `none` = LCNF lowers `eval`. -/
  ocaml    : Option String
  /-- The pinned rc.112 or Lean definition the spelling transcribes. -/
  cite     : String
deriving DecidableEq, Repr

def spec : NativeAtom → Spec
  | .succ => { name := "succ", arity := some 1, scheme := .mono [.nat] .nat,
               constGen := false, ts := "(n: number): number => n + 1", ocaml := none,
               cite := "Lean Nat.succ" }
  …                                     -- one row per constructor, the compiler forces all

def name  (a : NativeAtom) : String     := (spec a).name
def arity (a : NativeAtom) : Option Nat := (spec a).arity
def typeOf (a : NativeAtom) : List Ty → Option Ty := (spec a).scheme.apply
-- `eval` stays a match on the enum: see §6.
```

Answering the four sub-questions:

**(a) projections.** `name`, `arity`, `constGeneric` and `typeOf` become projections of `spec`
exactly as written above. The cost is real but small: `name` is a match today
(`Machine/Term.lean`, the `name` definition), and `ofName?_name` is proved by
`cases atom <;> rfl` — after the change it is still `cases atom <;> rfl`, because `spec` is a
match too and reduces the same way. `typeOf_mono` (`Program/NativeAtom.lean:99-111`) becomes a
statement about `Scheme.mono` and loses its per-atom `match tys with` gymnastics.

**(b) typing soundness proved once.** Today soundness is `nativeAtom_typed`
(`src/Effect4/Laws/Program/Typed.lean:586-749`), **165 lines** of hand proof with one block per
atom — I counted the range. That is the cost centre: 17 new atoms means 17 more blocks in the
same theorem. The design that collapses it:

```lean
/-- The per-atom obligation, one statement for every atom. -/
def Sound (a : NativeAtom) : Prop :=
  ∀ (tys : List Ty) (ty : Ty) (vs : List Val),
    a.typeOf tys = some ty → Fits vs tys →
      ∃ v, a.eval vs = some v ∧ Val.hasTy v ty = true

/-- The generic lemma for the monomorphic family: subsumption at each parameter is
    discharged once, by `hasTy_sub`, and the atom only has to answer on the
    parameters' own values. -/
theorem sound_of_mono {a : NativeAtom} {params : List Ty} {answer : Ty}
    (hs : (spec a).scheme = .mono params answer)
    (hev : ∀ vs, Fits vs params → ∃ v, a.eval vs = some v ∧ Val.hasTy v answer = true) :
    Sound a
```

and then, one level further, the shape lemmas that make `hev` free for a whole family:

```lean
/-- The evaluation shapes the monomorphic atoms actually have. -/
inductive Shape | nat1 | nat2 | natRel | bool1 | bool2 | natTest | str2 | strRel

theorem sound_of_shape {a : NativeAtom} {s : Shape}
    (hs : (spec a).scheme = s.scheme) (heval : ∀ vs, a.eval vs = s.run a vs) : Sound a
```

With `sound_of_shape`, `sub`, `mul`, `div` and `mod` cost **one `rfl` each** rather than one
proof block each, because they all share `Shape.nat2`; `le` and `gt` would share `Shape.natRel`
(and §5 recommends deriving them instead of adding them). `nativeAtom_typed` becomes
`fun atom => by cases atom <;> first | exact sound_of_shape rfl (by intro vs; rfl) | …` with a
hand block only for the atoms whose scheme is `.custom`.

**Honest cost and risk.** The brief asks whether the per-atom obligation is dischargeable by
`decide`. It is **not**, and no design makes it so: `Sound a` quantifies over all `Ty` and all
`Val`, both infinite, so there is no `Decidable` instance and `decide` cannot see it. What *is*
decidable is the *shape assignment* (`(spec a).scheme = s.scheme` closes by `rfl`), and that is
where the mechanisation lives. `aesop` can close the residual obligations if the inversion
lemmas are registered — `Fits.singleton_inv`, `Fits.pair_inv`, `Fits.all_sub_string`
(`Laws/Program/Typed.lean:376`, `:410`, `:397`) and `Val.hasTy_nat_inv`/`_bool_inv`/`_string_inv`
(`:74`, `:81`, `:88`) are exactly the rules the 165-line proof applies by hand, over and over.
There is **no named aesop rule set in the tree today** (I searched `src` for
`declare_aesop_rule_sets` and found none; `Laws/Program/Template.lean` passes rules per call,
e.g. `:29`, `:40-41`). Declaring one — say `atomSound` — with those six as `safe destruct`
rules is the instrument this chore asks for the second time, and the owner's standing rule says
to build it now. Second risk: a `Spec` record with eight fields means every new atom touches one
place, which is the point, but it also means the record's `DecidableEq` is derived over a
`String`-heavy structure, and `decide` on a `spec` equality will be slow if anything ever does
it at scale; keep `#guard`s on individual fields, not on whole rows.

**(c) exhaustiveness is already automatic, and `all` should be generated.** `all_complete` is
proved by `cases atom <;> simp [all]` (`Machine/Term.lean`, `all_complete`), and `covers_iff`
(the consumer-inventory law) is proved beside it. That is the good half. The bad half is that
`all` is a hand-written list whose only guard is the theorem — a new constructor left out of
`all` fails `all_complete`, which is correct but is a compile error in a *proof*, not in the
table. Recommend: emit `all` from the constructor list in `tools/Effect4Gen`, which already
does exactly this kind of reflection — `Effect4Gen.Rows.ctorParams`
(`tools/Effect4Gen/Rows.lean:38-45`) reads a constructor's fields by `getConstInfoCtor` and a
`forallBoundedTelescope`. Keep `all_complete` as the acceptance guard on the generated file.

**(d) the faces are generated, except the one that matters most.** Read at the files:

| face | generated? | from what |
| --- | --- | --- |
| TS profile `atoms` array | yes | `tools/Tools/TsGen.lean:543-552`, `atomRows := NativeAtom.all.map fun a => (a.name, a.arity, a.mono)` |
| OCaml `atom_names`, `const_atoms` | yes | `ocaml/eff/eff_native.ml:7-11`, generated by `src/OCaml5/Tools/EffGen.lean` |
| OCaml evaluator | yes, from LCNF | `ocaml/engine/api_engine.ml:2808-2809` is `program_native_atom_eval`, lowered from `NativeAtom.eval` (§6) |
| **TS prelude (the atoms' meaning on the host)** | **no — hand-written** | `harness/truth/prelude.ts:1-31` says so in its own header: "Hand-written transcription (no generator exists for it yet); when either Lean table changes, this file changes with it, and the self-test refuses an atom it does not export" |

The `ts` field of `Spec` exists to close that last row. The prelude's 39 `selfTestCases`
(`harness/truth/prelude.ts:151-195`) are checked against the profile's atom set by
`run-truth.ts`, so an atom appended in Lean cannot stay *untested* — but it can stay *unwritten*
until someone writes it, and the failure mode is a red harness rather than a generated file.
Moving the one-line bodies into `Spec.ts` and emitting the prelude's atom block as a new
generator group (beside `Rows`/`Forms` in `tools/Effect4Gen/manifest.json`, which has 21 groups
and takes a new one as "an entry here and no code change in the driver", per the manifest's own
comment) makes the atom alphabet single-source across all four faces.

**The trust gate is not a constraint on any of this.** The gate's token list is
`["unsafe", "partial", "sorry", "axiom", "native_decide", "extern", "implemented_by"]`
(`Test/Audit/AxiomGate.lean:243-244`), plus a bodyless `opaque` (`:47-55`) and an unadmitted
`Classical.choice` dependency. A record of strings and enums, a match on an enum, and a
structural `Scheme.apply` need none of them. The one place the gate has bitten this alphabet
before is `deriving Repr` on a `List`-nested inductive, which produces a `partial` definition —
`Store.Val`'s `Repr` is hand-written for exactly that reason (`src/Effect4/Store/Val.lean:173-176`).
`Spec` is not nested, so `deriving Repr` is fine on it; a `Scheme` carrying a `List Ty` is also
fine, because `Ty` is not nested (that is why rows 42/43 step 1 chose `refOf`/`deferredOf` over
`Ty.app`, `plan` §1).

## 2. Polymorphic atoms without lambdas

### 2.1 The scheme language already exists — it landed six hours ago

This is the strongest finding in the note. The "small scheme language: argument patterns with
metavariables, subsumption, join" that the brief asks me to design **is the row-template calculus
of step 2**, already in the tree:

- `Ty.var (index : Nat)` — a template parameter, `normalize` the identity, `hasTy` always false
  (`Program/Ty.lean:51-54`; the `hasTy` arm at `Program/Typed.lean:67`, read as `| .var _ => false`).
- `Ty.Subst := List (Nat × Ty)` (`Ty.lean:442`).
- `Ty.instantiate (σ) : Ty → Ty`, with an unbound parameter going to `never` (`Ty.lean:447-466`).
- `Ty.infer (σ) : Ty → Ty → Subst`, binding a parameter **at its first occurrence**
  (`Ty.lean:472-484`) — which is LLVM's `LLVMMatchType<0>` and TypeScript's own inference.
- `Ty.matchTemplate (σ) (template request) : Option Subst` = infer, then guard by `sub`
  (`Ty.lean:489-491`), whose law is its own guard: `matchTemplate_sound` is **proved**
  (`Laws/Program/Template.lean:54-57`, by `unfold` + one `aesop`).

So the atom table's typing scheme should be the **same** objects the rows use. That is the
"top of the abstraction tree" answer: one template calculus, two consumers.

```lean
/-- An atom's typing scheme as data. `params`/`answer` are `Ty` over `Ty.var`. -/
inductive Scheme
  /-- Fixed parameters, fixed answer; each argument at a subtype (today's `mono`). -/
  | mono (params : List Ty) (answer : Ty)
  /-- Any number of arguments at one parameter type (today's `strings`). -/
  | variadic (param : Ty) (answer : Ty)
  /-- A template over `Ty.var`, parameters bound by `inferJoin`, answer instantiated. -/
  | poly (params : List Ty) (answer : Ty)
  /-- Alternative signatures, first hit wins (today's `eq`: two naturals or two strings). -/
  | alts (cases : List (List Ty × Ty))
  /-- The residue: an atom whose typing is a named function (`fst`, `snd`, the cause queries). -/
  | custom (tag : CustomScheme)
deriving DecidableEq, Repr

def Scheme.apply : Scheme → List Ty → Option Ty
  | .mono params answer, tys =>
      if tys.length = params.length ∧ (tys.zip params).all (fun (a, e) => a.sub e)
      then some answer else none
  | .variadic param answer, tys => if tys.all (·.sub param) then some answer else none
  | .poly params answer, tys => do
      let σ ← Ty.matchTemplateArgs [] params tys
      some (answer.instantiate σ).normalize
  | .alts cases, tys => cases.findSome? fun (params, answer) => (Scheme.mono params answer).apply tys
  | .custom tag, tys => tag.apply tys
```

with the list-level match folded from the existing one:

```lean
/-- Match an argument list against a parameter template list, threading the bindings. -/
def Ty.matchTemplateArgs (σ : Subst) : List Ty → List Ty → Option Subst
  | [], [] => some σ
  | p :: ps, r :: rs => do let σ' ← Ty.matchTemplate σ p r; Ty.matchTemplateArgs σ' ps rs
  | _, _ => none
```

### 2.2 The one generalisation the atoms need: `infer` must join, not keep the first

`ite : bool → A → A → A` "typed at the join" does not work with `Ty.infer` as written.
`infer` binds `A` at the first occurrence and then `matchTemplate`'s guard asks
`sub request (instantiate σ' template)`; for `ite(b, 1, "x")` that guard is
`sub (prod bool (prod nat string)) (prod bool (prod nat nat))`, which is false, so the
application is refused where TypeScript answers `number | string`. The fix is one function:

```lean
/-- `infer`, accumulating by the canonical join at a repeated parameter. Used by the atom
    schemes; the rows keep `infer`, whose first-occurrence rule is what an invariant handle
    position needs (decisions row 55). -/
def Ty.inferJoin (σ : Subst) : Ty → Ty → Subst
  | .var i, r => match σ.lookup i with
      | some t => σ.map (fun (j, u) => if j = i then (j, Ty.join u r) else (j, u))
      | none   => σ ++ [(i, r)]
  | .option t, .option r => inferJoin σ t r
  | .list t,   .list r   => inferJoin σ t r
  | .prod a b, .prod c d => inferJoin (inferJoin σ a c) b d
  | …                                       -- the same congruence arms as `infer`
  | _, _ => σ
```

I traced three cases by hand against the definitions as read:

| application | template | σ after `inferJoin` | guard | answer |
| --- | --- | --- | --- | --- |
| `ite(b, 1, "x")` | `[bool, var 0, var 0] → var 0` | `0 ↦ join nat string` | `sub nat (nat\|string)` and `sub string (nat\|string)`, both true by `sub`'s right-union arm (`Ty.lean:419`) | `nat \| string` |
| `cons(1, xs : list string)` | `[var 0, list (var 0)] → list (var 0)` | `0 ↦ join nat string` | `sub (list string) (list (nat\|string))` true by `sub`'s list arm (`:422`) | `list (nat\|string)` |
| `head(xs : list nat)` | `[list (var 0)] → option (var 0)` | `0 ↦ nat` | `sub (list nat) (list nat)` true by reflexivity (`:415`) | `option nat` |

Note what falls out: `cons : A → list B → list (join A B)`, which the brief spells with an
explicit `join` in the answer, needs **no** join former in the scheme language — writing both
occurrences as `var 0` and letting `inferJoin` do the widening is the same thing and keeps the
scheme first-order. That is a genuine simplification of the brief's own proposal.

### 2.3 The generic soundness lemma for the polymorphic family

```lean
/-- A `poly` scheme's soundness, once. The `hev` premise is the atom's own content: on
    values fitting the *instantiated* parameters it answers a value of the instantiated
    answer. Subsumption at the call site is discharged here, by `matchTemplate_sound`
    and `hasTy_sub`, exactly as `sound_of_mono` discharges it for the monomorphic family. -/
theorem sound_of_poly {a : NativeAtom} {params : List Ty} {answer : Ty}
    (hs : (spec a).scheme = .poly params answer)
    (hev : ∀ (σ : Ty.Subst) (vs : List Val),
             Fits vs (params.map (Ty.instantiate σ)) →
               ∃ v, a.eval vs = some v ∧ Val.hasTy v ((answer.instantiate σ).normalize) = true) :
    Sound a
```

The proof obligation the lemma leaves is genuinely per-atom and genuinely semantic — for
`head` it is "a value fitting `list A` has a first element of type `A` or is empty", which is
where the `fiberSnapshot` trap of §4.3 lives. But it is stated once per atom instead of
re-deriving subsumption each time, and `hasTy_normalize` (proved, extended at step 1 per the
plan's §2a) closes the `normalize` on the answer.

There is one honest gap in `sound_of_poly` as stated: it quantifies over an arbitrary `σ`, while
`Scheme.apply` only ever supplies the `σ` that `matchTemplateArgs` produced. That makes the
premise *stronger than needed* and therefore harder to prove for an atom whose evaluation cares
which types it got (none of the proposed atoms do — they are all parametric in the payload). If
one ever does, the lemma needs the match hypothesis threaded in, which costs a second form of
the lemma, not a redesign.

### 2.4 Where this hits the literal rule (DI-15, `litArgTy`, const-generic `pair`)

The literal rule is applied *before* the scheme sees anything. `argTy` passes the enclosing
atom's own const flag down to its direct arguments and nowhere else:
`argsTy sig env (sig.constAtom atom) args` (`Program/Typing/Rules.lean:92-94`), and
`litArgTy const` keeps a string literal as `lit s` only when `const` is true
(`:77-81`). `constAtom` is `NativeAtom.constGeneric`, true only for `pair`
(`Program/NativeAtom.lean:29-33`), lifted by name in `nativeConstAtom` and pinned
`nativeConstAtom_pair` by `decide` (`Program/Native.lean:38-41`).

Three consequences for the new atoms, all decisions someone has to make:

1. **`ite` must not be const-generic.** If it were, `ite(b, "A", "B")` would type at
   `lit "A" | lit "B"`, and the corresponding TS would need `<const A>` parameters. Leaving it
   non-const gives `string`, which is exactly what TypeScript infers for a conditional
   expression at a non-`const` type parameter. Recommend non-const, matching every atom but
   `pair`.
2. **`some` must not be const-generic either**, for the same reason, and this one has a visible
   cost: `some("A")` types at `option string`, so a program that wants `option (lit "A")` cannot
   say it. That is the same cut the cut's §1 already records for `succeed "x"`; no new hole.
3. **`pair`'s scheme is `poly [var 0, var 1] (prod (var 0) (var 1))`** and this is *not* the
   same as today's `typeOf` arm `| .pair, [a, b] => some (.prod a b)` under `inferJoin` — it is,
   because the two parameters are distinct variables so no join ever fires. Worth a `#guard` that
   `typeOf .pair [.lit "A", .string] = some (.prod (.lit "A") .string)`, since that exact
   equation is what DI-55 and the `eq (fst (pair "A" m)) "A"` idiom depend on
   (`Program/NativeAtom.lean:61-71`, the docstring).

**Which atoms do not fit the scheme language, honestly.** `fst` and `snd` distribute over
unions and join the selected columns (`projectProduct`, `Program/NativeAtom.lean:48-59`); no
template does that, because `infer` on `(.prod a b, .union c d)` falls through to the catch-all
and binds nothing (`Ty.lean:484`). The four cause queries read `causeInputError?`
(`Program/NativeAtom.lean:19-21`), also not a template. `getOrElse` compares *normalized*
subsumption (`:92`). So `Scheme.custom` must exist, and it will hold five or six atoms whose
soundness stays a hand proof — the ones already proved
(`Laws/Program/Typed.lean:665-670`, `:689-708`, `:741-746`). That is the honest ceiling: the
declarative table covers the atoms we are *adding*, and leaves the awkward ones we already have
exactly as costly as they are today. It does not make them worse.

## 3. Binder terms as first-order data

### 3.1 What our device is, in the literature's words

Our device is **defunctionalization** (Reynolds 1972, *Definitional interpreters for
higher-order programming languages*) already performed, plus **closure conversion with the
environment passed as a list**, and it is worth saying so precisely because it explains why no
new value kind is needed.

- `NativeAtom` **is** the defunctionalized function space: a closed, finite set of tags for the
  functions a program may name, and `NativeAtom.eval` is the `apply` function. Defunctionalizing
  a *closed* program is exactly what Reynolds's transformation does; our atom table is its result
  taken as the source language rather than as a compiler output. This is why the language has no
  lambda and needs none for the atoms.
- A **binder term** is not a closure and does not need closure conversion in the usual sense:
  it has no captured environment of its own. `Term.scoped n` (`Machine/Term.lean`, the mutual
  `Term.scoped`/`Terms.scoped` block) says every variable is below level `n`, so a term carried
  by an operation is a term over the *caller's* environment extended at the end. What the store
  operation carries alongside it — `SyncOp.refUpdate (cell) (f : Term) (env : List Val)` in the
  plan (§1, §2b) — is the caller's environment, a list of first-order values. So the design *is*
  closure conversion, with the environment record spelled as `List Val` rather than as a heap
  object. Saying it that way is the honest framing: we pay closure conversion's cost (the env is
  copied into the op) and get its benefit (the op stays data, so the step stays atomic and the
  wire stays first-order).
- **Lambda lifting** is what we are *not* doing, and should not: lifting `(a) => a + x` to a
  top-level `f(a, x)` would require a name space of program-level functions, which DI-20/DI-28
  refuse for a stored program (`docs/core/language-cut.md` §1, §6).

For first-order IRs the comparison is instructive and cuts our way:

- **LLVM** has no nested functions at all; a "function argument" is a pointer value plus a
  signature, and any intrinsic that conceptually takes a callback (`llvm.experimental.*`) either
  takes a real function pointer or has the body inlined at the call site. Our `Ref.update`
  is the second case: the function is syntactically present at the perform site, so the right
  representation is the *inlined block*, not a reference.
- **Cranelift** likewise: `call_indirect` takes a `SigRef` plus a value; there is no closure.
- **WebAssembly** is the closest analogue to what we would need if a function ever had to be
  stored: `funcref` + `call_indirect` through a table index *is* defunctionalization written into
  a specification. Our equivalent, if it is ever wanted, is already named by the cut: "a program
  as a value is a `Val.ref` to its digest, run by a row" (`language-cut.md` §1, third row). We do
  not need it for row 43, and should not reach for it.

### 3.2 The typing rule for a row that takes a function

`perform` types today as: type the request, then `rowTy row r`
(`Program/Checker.lean:131-137`), and `rowTy` is match-then-instantiate
(`Program/Typing/Rules.lean:114-117`). The plan's §2b says `matchTemplate` takes a seed for
exactly this reason. The rule, written out:

```lean
/-- A row's function column: the parameter and result templates, over the row's own
    variables. `none` for the rows that take no function. -/
structure Row where
  …
  fn : Option (Ty × Ty) := none

/-- The type of a row performed on a request of type `r`, with the operation's binder term.
    The term is typed at the environment extended by the *instantiated* parameter — the same
    device `iterate` uses for its `step` — and the result column extends the bindings by the
    same `matchTemplate`, so `modify : A → [B, A]` binds `B` from the term's own type. -/
def rowTyFn (sig : Signature Op) (tys : TyEnv) (row : Row) (r : Ty) (f? : Option Term) :
    Option EffTy := do
  let σ ← Ty.matchTemplate [] row.request.normalize r.normalize
  match row.fn, f? with
  | none, _ => some ⟨(row.answer.instantiate σ).normalize,
                     (row.error.instantiate σ).normalize, Requirement.ofList row.requires⟩
  | some (param, result), some f => do
      let a ← some ((param.instantiate σ).normalize)
      let b ← termTy sig (tys ++ [a]) f                 -- the binder is the LAST position
      let σ' ← Ty.matchTemplate σ result b              -- extend, seeded by σ
      some ⟨(row.answer.instantiate σ').normalize,
            (row.error.instantiate σ').normalize, Requirement.ofList row.requires⟩
  | some _, none => none                                -- a function row with no term: refused
```

The four `Ref` row families and what they need:

| row | `request` | `fn` | answer |
| --- | --- | --- | --- |
| `refUpdate` | `refOf (var 0)` | `some (var 0, var 0)` | `unit` |
| `refGetAndUpdate`, `refUpdateAndGet` | `refOf (var 0)` | `some (var 0, var 0)` | `var 0` |
| `refUpdateSome`, `refGetAndUpdateSome`, `refUpdateSomeAndGet` | `refOf (var 0)` | `some (var 0, option (var 0))` | `unit` / `var 0` / `var 0` |
| `refModify` | `refOf (var 0)` | `some (var 0, prod (var 1) (var 0))` | `var 1` |
| `refModifySome` | `refOf (var 0)` | `some (var 0, prod (var 1) (option (var 0)))` | `var 1` |

Read this against the trap the prelude already records: `harness/truth/prelude.ts:24-30` says in
so many words that `Ref.modify(ref, takeAndBump)` prints the **total** shape `(a) => a` where
rc.112 wants `(a) => [b, a']`, that this misbehaves on rc.112, and that it is recorded as finding
F3 and **not patched**. Binder terms fix that defect by construction: `refModify`'s `fn` result
template is `prod (var 1) (var 0)`, so a term that does not have a pair type is refused by the
checker, and the printed lambda's body is the pair. That is a real bug closed by this design, and
it is the best argument for it.

### 3.3 What the printer prints and the reader reads

**Printing.** The fn name is carried today as text in `Row.trailing : List String`, and
`printRow` maps it straight to `.ident` (`Codegen/PrintLeaf.lean:266`, then `:272`/`:275`). For a
binder term the printed argument is a lambda whose parameter is the *next level's* name:

```lean
-- inside the row-call clause, at environment length n
let binder : TypeScript.Parameter := ⟨Var.name n, none⟩
let lambda := TypeScript.Expr.lambda [binder] (printTerm f)
```

`Var.name index = "a" ++ toString index` (`Codegen/PrintLeaf.lean:152`). One interface change is
needed and it is cheap: `printRow` takes only `(row) (request)` today
(`PrintLeaf.lean:265`), while the level `n` *is* in scope at the call site —
`print sig n (.perform op request) = printRow (sig.rowOf op) request`
(`Codegen/Print.lean:46-47`). So `printRow` gains an `n` and an `Option Term`, and the
`rowCall` row of `Codegen/Templates.lean` passes them. `LambdaShape` and `atom?`
(`Codegen/Forms.lean:126-149`, `Codegen/Styles.lean:128-135`) retire, and with them the four
`#guard`s at `Styles.lean:226-227`.

**Reading.** `readTerm n x` reads *at a level*: an identifier is a variable when
`Var.read n s` finds it, searching levels `n-1` down to `0` by string comparison and decoding no
digits (`Codegen/Read.lean:103-107`). The reader's own binder machinery is already level-based
and already proved injective: `Var.name_inj` (`Read.lean:1096`), `Var.read_sound`
(`:1114`), `Var.read_name` (`:1122`), `Var.read_none` (`:1132`). So reading
`Ref.update(a0, (a1) => add(a1, a0))` at level `1` means: read `a0` at level 1 → `var 0`; see the
lambda, check its parameter is exactly `Var.name 1`, read the body at level `2`. A parameter that
is not the expected name is already a refusal the reader can spell —
`ReadRefusal.binder (expected : String)` exists (`Read.lean:57-58`): "A lambda, `const` or
`step` parameter that is not the binder due at that position."

**The template table takes it as one row.** `Codegen/Forms.lean`'s `TermTemplate.here k`
expands to `.var (n + k)` (`Forms.lean:28`, `:51-54`) — the table already speaks levels, so a
lambda skeleton is a new `ArgClass` (`Forms.lean:17-18` currently has nine) plus a
`TermTemplate.here 0` in the expansion, with no new mechanism.

### 3.4 Nesting cannot capture, and the reason is structural

The answer is: **de Bruijn levels, not indices**. `Var.name` is the absolute level
(`PrintLeaf.lean:152`), `readTerm`'s `n` is the number of binders in scope
(`Read.lean:105-107`), and `Template.here k = var (n + k)` (`Forms.lean:54`). Under levels, a
variable's name never changes when a binder is pushed, so there is nothing to shift and nothing
to capture. A function inside `iterate`'s step inside a row's function indexes as:

```
env length n                       ...  a0 … a(n-1)
row's function binds the cell's value      a(n)      -- term typed at tys ++ [A]
iterate's cursor                           a(n+1)    -- test/step/result at env ++ [cursor]
iterate's body answer (step only)          a(n+2)    -- step at env ++ [cursor, answer]
```

and that is exactly what the checker already does for `iterate`
(`Program/Checker.lean:178-189`: `term? sig (env ++ [cursor])` for `test`, then
`(env ++ [cursor, b.answer])` for `step`) and for `acquireRelease`
(`:201-205`: `check sig (env ++ [a.answer, .exitOf a.answer a.error])`). Every new binder goes at
the **end**, and that is why it is free: `Var.weaken cut index = if index < cut then index else index + 1`
(`Program/Eff.lean:450`) is the insert-in-the-middle operation, needed only when a *derived form*
inserts a binder before existing ones (`Forms.insert`, `Forms.lean:56-59`), and appending at the
end never triggers it. `argTy_weaken`/`termTy_weaken` are **proved**
(`Typing/Rules.lean:297-321`), so the weakening that derived forms do need is already lawful.

### 3.5 The one cost nobody has named yet: the generated scope fold must look inside the op

This is the finding to carry back. `Eff.scopedAt`'s `perform` arm is
`eff_perform := fun _ a1 n => a1.scoped n` (`src/Effect4/Program/Scoped.lean:26`), with the
simp lemma `Eff.scopedAt_perform : Eff.scopedAt n (.perform a0 a1) = a1.scoped n`
(`:120-121`) — the operation is **ignored**, because today an operation carries only a `FnName`,
a `FinalizerStrategy` or an external index, none of which mention a variable. Once `NativeOp`
carries a `Term`, that arm is **wrong**: a row could carry a term with an out-of-scope variable
and `Eff.scoped` would say yes.

`Scoped.lean` is generated (`tools/Effect4Gen/Authoring.lean`, group `Scoped` in
`manifest.json`), and the scope-safety landing (memory: `scopedAlgebra` via `cata_eff`, 48
generated lift lemmas, `authoring_scoped` dispatcher tactic) means the fix has to be made in the
generator, not by hand. The shape:

```lean
/-- Every variable the operation's own terms mention is below `n`. -/
def NativeOp.scopedOp (n : Nat) : NativeOp → Bool
  | .refUpdate f | .refGetAndUpdate f | … | .refModifySome f => f.scoped n
  | _ => true

-- the generated algebra's perform arm becomes, for a signature with an op scope check:
eff_perform := fun op a1 n => a1.scoped n && Signature.scopedOp op n
```

which needs `Signature` to carry a `scopedOp : Op → Nat → Bool := fun _ _ => true` field so the
fold stays generic in `Op` (it is `Eff Op` for an abstract `Op`, and `Scoped.lean` must not name
`NativeOp`). **Cost and risk:** `Signature` gains a field with a default, so every construction
of a `Signature` still compiles; but the 48 generated lift lemmas and `elaborate_scoped` are
stated over `Eff.scopedAt`, and changing its `perform` arm changes their statements' *content*
even where the syntax does not move. The honest cost is: regenerate the `Scoped`,
`ScopedLaws` and `Authoring` groups, and expect the `perform` lift lemma to need the new
conjunct discharged (`rfl` for every authored wrapper, since `Rows.lean`'s wrappers build the op
with no term today and with a supplied term after L4). If the `perform` arm is *not* fixed, the
defect is silent and reaches the printer — the printer would emit a lambda mentioning `a7` in a
program with three binders. Recommend fixing it **in the same commit** that puts a `Term` in
`NativeOp`, and pinning it with a red control: a `#guard` that
`Eff.scopedAt 1 (.perform (.refUpdate (.var 5)) (.var 0)) = false`.

## 4. Totality and the frontier

### 4.1 What totality means here, and what is proved

Two theorems carry it, both **proved**, both in the same mutual block style:

- `evalTerm_isSome` (`Laws/Program/Typed.lean:830-856`): under `Fits env tys` and
  `termTy nativeSignature tys t = some ty`, `(evalTerm env t).isSome = true`. A well-typed term
  over a fitting environment always evaluates.
- `evalTerm_hasTy` (`:774-796`): and its value has the type.

Both go through `nativeAtom_typed` (`:586`), whose conclusion is
`∃ v, nativeAtom atom vs = some v ∧ Val.hasTy v ty = true` — the existential is what supplies
*both* halves at an application. So **every new atom must make `eval` total on the values its
scheme admits**, or `evalTerm_isSome` breaks. That is the real constraint, and it is stronger
than "`eval` returns `Option`": the `Option` is for values the scheme does *not* admit.

`evalTerm`'s `none` is a frontier, not a failure — the project's standing convention, stated at
`Machine/Stores.lean:845-846` for a dangling `Ref` key ("a dangling key is a frontier, never a
typed error (`AGENTS.md`)") and at `Program/Compile.lean:560-562`, `:579-584`, where an
unevaluable term becomes `badShape`.

### 4.2 The three arithmetics, read at each face

| face | `n / 0` | `n % 0` | `a - b` | overflow |
| --- | --- | --- | --- | --- |
| Lean `Nat` | `0` | `n` | `max 0 (a-b)` | none, unbounded |
| OCaml engine | `0` | `n` | `max 0 (a-b)` | saturating at `max_int` for `pow`/`shiftLeft`/literals; **raw `*` for `Nat.mul`** |
| TypeScript host | — | — | `pred` is guarded (`prelude.ts:42`) | exact to `2^53 - 1`, then float |

Evidence: the OCaml column is `OCaml5.Lcnf.Translate.builtin?`
(`src/OCaml5/Lcnf/Translate.lean:162-163` for `div`/`mod`, guarded inline;
`:164-166` for `sub`; `:161` for `mul`, plain `bin "*"`), backed by the hand module
`ocaml/engine/e4_nat.ml:48-49` (`div b=0 → 0`, `rem b=0 → a`) whose properties N2 and N3 are
documented and marked *tested* at `ocaml/engine/e4_nat.mli:15-18`. The TS column is
`Effect4.Program.rc112.natBound = 2^53 - 1` (`Program/Profile.lean:140-142`), whose docstring
says why: "above it the host's `+` stops being exact (`harness/truth/prelude.ts`, `add`), which
is the arithmetic DI-56 rules on" (`:129-130`).

**Two corrections to the tree's own documents, found by reading.** Both say the division guard
is missing when the translator has it:

1. `ocaml/gen/NOTES.md:255` — "`Nat.div/mod` by zero (`0` in Lean, `Division_by_zero` in OCaml)
   is **still not guarded**". `Translate.builtin?` guards both (`Translate.lean:162-163`).
2. `ocaml/engine/externs.txt:157-162` — "`Translate.builtin?` emits raw `/` and `mod`, which
   RAISE where Lean answers 0 and n"; the two `fn?` rows routing `Nat.div → E4_nat.div` and
   `Nat.mod → E4_nat.rem` are marked optional because "no declaration in this root set divides".
   The routing is right and agrees with the inline guard, so either path is correct; the *reason*
   given is stale.

Consequence for the atoms: **`div` and `mod` are safe on the OCaml face today**, which is the
opposite of what a reader of those two documents would conclude. Recommend the main session
correct both lines while it is in the area; and flip the two `fn?` rows to `fn` when `div`/`mod`
atoms land, so the guard is enforced by the one mechanism rather than by two that could drift.

**`mul` is the one that is not safe.** `Nat.mul` lowers to OCaml's `*`
(`Translate.lean:161`), which wraps silently at 63 bits, while the very next comment in the file
says "Clamp the multiplication too; clamping only the power still allowed a wrap"
(`:177`) — and that clamp is inside `Nat.shiftLeft`'s own row, not in `Nat.mul`'s. So a `mul`
atom reaches an unclamped multiplication on the engine face. Recommend: give `Nat.mul` the same
clamped form `shiftLeft` uses, in the commit that adds the `mul` atom. On the TS face, `mul`
makes the `2^53` bound reachable in 54 doublings where `add`/`succ` need `2^53` steps, and
`natBound` is **not enforced inside `evalTerm`** — `admitsNat` is applied only at the abstract
host boundary (`Program/HostBoundary.lean:61`, in `Profile.Scalar.checkRequest`) and pinned by
two `#guard`s in `Test/Program/HostSpecContract.lean:89-90`. That is a pre-existing gap that
`mul` makes cheap to hit; it is not a reason to refuse `mul`, but it should be said on the
surface (the profile already has the field to say it with).

### 4.3 The totality trap the list atoms walk into

This is a concrete counterexample, assembled by reading three files, and it breaks
`evalTerm_isSome` if the obvious `eval` arms are written.

`Val.hasTy v (.list t)` accepts **two** frames (`Program/Typed.lean:84-91`):

```lean
| .list ty =>
  match v with
  | Value.fiberSnapshot _ =>
    match Val.snapshot? v with
    | some ids => ids.all (fun id => Val.hasTy (Val.fiber id) ty allocated)
    | none => false
  | .list values => values.all fun x => Val.hasTy x ty allocated
  | _ => false
```

and `Value.fiberSnapshot fibers` is `.ctor 3 [fibers]`
(`Machine/Value.lean:216`), **not** a `.list`. Meanwhile
`Action.snapshotChildren` types at `list (fiberOf (handle "unknown") (handle "unknown"))`
(`Program/Checker.lean:360-361`) and its runtime answer is built by
`Value.fiberSnapshot ((Image.list Value.fiberHandle).toVal ids)`
(`Machine/Alphabets.lean:220-223`). So:

```
bind (withFiber snapshotChildren) (sync (app "length" [var 0]))
```

is **well typed** (`length : list A → nat` binds `A := fiberOf …`), and its environment holds a
`.ctor 3 [...]`. A naive `| .length, [.list vs] => some (.nat vs.length)` answers `none`, so
`evalTerm` answers `none`, so `evalTerm_isSome` is false and the typed-state invariant loses its
totality half. The same program with `head`, `tail`, `get` or `isEmpty` has the same shape.

**The fix, one deep helper and one inversion lemma:**

```lean
/-- Every value the type `list _` admits, as a list. Both frames: the carrier's own `list`
    and the fiber snapshot (`Value.fiberSnapshot`, `Val.snapshot?`). Every list atom reads
    its argument through this and nothing else. -/
def Val.asList? : Val → Option (List Val)
  | .list values => some values
  | v => (Val.snapshot? v).map (·.map Val.fiber)

/-- The inversion the list atoms' soundness cases begin with. One lemma, N atoms. -/
theorem Val.hasTy_list_inv {v : Val} {t : Ty} (h : Val.hasTy v (.list t) = true) :
    ∃ vs, Val.asList? v = some vs ∧ ∀ x ∈ vs, Val.hasTy x t = true
```

`hasTy_list_inv` does not exist today — I searched `src` for `hasTy_list` and for
`hasTy.*list.*inv` and found nothing; the eleven inversions that do exist are
`unit`/`nat`/`bool`/`string`/`lit`/`option`(two forms)/`refTy`/`deferredTy`/`prod`(two forms)
at `Laws/Program/Typed.lean:67-160`. The snapshot branch of the proof is supplied by
`snapshot?_fibers` and `snapshot?_exact`, both **proved**
(`Machine/Alphabets.lean:324-334`).

**Honest cost.** `asList?` means the OCaml and TS faces must read both frames too, or the three
disagree on `length(snapshot)`. On the TS face the snapshot is a plain array of fiber objects, so
`length` is already right there; the disagreement would be Lean-side only. The cheaper
alternative is to **refuse** the snapshot at the atom's type — i.e. keep `eval` on `.list` only
and add a checker rule that a list atom's argument may not be typed
`list (fiberOf _ _)`. I recommend **against** it: it is a special case in the type system to
protect a representation choice, and the very next `Value.ctor`-framed list (a `Queue` snapshot,
a `PubSub` drain — both named as absent in `language-cut.md` §4) would need the same patch.
`asList?` is one deep definition that absorbs the next one for free.

### 4.4 The second representation overlap, which is safe but should be pinned

`pair` builds `Val.list [a, b]` (`Machine/Term.lean`, `eval`'s `.pair` arm) and
`Val.hasTy v (.prod ta tb)` matches `.list [x, y]` (`Program/Typed.lean:80-83`). So one value
inhabits both `prod nat nat` and `list nat`, and `Val.pair a b` — a real constructor of the
carrier (`Store/Val.lean:157`) — is *not* what `prod` reads. Two notes:

1. It is **sound**, because the checker never lets a `prod` flow into a `list` parameter:
   `Ty.sub` has no `(.prod _ _, .list _)` arm and falls through to `| _, _ => false`
   (`Program/Ty.lean:416-430`). So `length(pair(1,2))` is a type error, which is what we want.
2. It is **invisible at the host**, where both are a two-element JS array, so the TS `length`
   would answer `2` for a program Lean refuses. That asymmetry only affects refused programs, so
   it is safe — but it is exactly the kind of thing a later `check-host` disagreement is blamed
   on. Recommend a pinned pair of `#guard`s in the atom contract: `Ty.sub (.prod .nat .nat) (.list .nat) = false`
   and `nativeAtomTy "length" [.prod .nat .nat] = none`.

### 4.5 Per-atom convention recommendations

| atom | convention | why, and which face is the constraint |
| --- | --- | --- |
| `sub` | Lean truncated, `max 0 (a-b)` | all three already agree: `Translate.lean:164-166`, `e4_nat.mli:18` N3, and `pred`'s prelude line `prelude.ts:42` is the same rule at 1 |
| `div` | Lean, `n / 0 = 0` | OCaml guarded (`Translate.lean:162`); TS needs `b === 0 ? 0 : Math.floor(a / b)` — JS `/` is float division, so `Math.floor` is load-bearing, not cosmetic |
| `mod` | Lean, `n % 0 = n` | OCaml guarded (`:163`); TS needs `b === 0 ? a : a % b` |
| `mul` | exact in Lean; clamp OCaml | fix `Nat.mul`'s row first (§4.2); TS is exact to `2^53` and the profile says so |
| `head`, `get` | answer `option A` | an `Option` answer keeps totality without a convention: the empty list and the out-of-range index are `Val.none`, a real carrier frame (`Store/Val.lean:158`). **Never** a frontier and never a default value |
| `tail` | answer `list A`, `tail [] = []` | total, no `Option` needed; matches JS `xs.slice(1)` on `[]` |
| `length`, `isEmpty` | total | via `asList?` (§4.3) |
| `ite` | eager in all three arms | the arms are *terms*, already evaluated before the atom; this is `getOrElse`'s own convention and its prelude line says so (`prelude.ts:65-69`, "Both call arguments are evaluated eagerly") |
| `concat` | `String.append` | `Translate.lean:205` lowers it to OCaml `^`; TS `+`. No traversal, so no axiom exposure (§5.3) |

## 5. What grows the atom families safely

The current inventory is **20 atoms** (`Machine/Term.lean`, `NativeAtom.all`), and the plan's L3
names **17** more (`plan` §2c, row L3). My first recommendation is to add **12**, not 17, and to
say for each cut why the language loses nothing.

### 5.1 The four the rows actually need (L4 is blocked on these and nothing else)

The plan's own probe found the minimum: `zeroWhenPositive = ite (lt 0 a) (some 0) none`,
`noChange = none`, `takeAndBump = pair a (succ a)`, `double = mul a 2` (`plan` §2b, "Step 3,
atoms"). So retiring `FnName` needs exactly `ite`, `some`, `none`, `mul`.

| atom | arity | scheme | `eval` arm | TS prelude line | risk |
| --- | --- | --- | --- | --- | --- |
| `ite` | 3 | `poly [bool, var 0, var 0] (var 0)` | `\| .ite, [.bool b, x, y] => some (if b then x else y)` | `export const ite = <A>(c: boolean, t: A, e: A): A => c ? t : e` | needs `inferJoin` (§2.2); **eager**, so it is a selection not a conditional — say so in the docstring, as `getOrElse`'s line does |
| `some` | 1 | `poly [var 0] (option (var 0))` | `\| .some, [v] => some (Store.Val.some v)` | `export const some = <A>(a: A): Option.Option<A> => Option.some(a)` | non-const-generic, so `some("A") : option string` (§2.4) |
| `none` | **0** | `mono [] (option never)` | `\| .none, [] => some Store.Val.none` | `export const none = (): Option.Option<never> => Option.none()` | first nullary atom — see below |
| `mul` | 2 | `mono [nat, nat] nat` | `\| .mul, [.nat a, .nat b] => some (.nat (a * b))` | `export const mul = (a: number, b: number): number => a * b` | `Nat.mul` lowers to unclamped OCaml `*` (§4.2); fix `Translate.lean:161` in the same commit |

**`none` is the first nullary atom and it is worth one paragraph.** Every atom today has arity
≥ 1 (`Machine/Term.lean`, `arity`; `strings` is variadic, i.e. `none`). The faces take it
without a change, which I checked: `printTerm (.app "none" .nil) = .call (.ident "none") []`
(`Codegen/PrintLeaf.lean:165-173`), which renders `none()`; and the reader's app arm is
`| .call (.ident atom) args => (readTerms n args).map (.app atom)` with
`readTerms n [] = .ok .nil` (`Codegen/Read.lean:152`, `:157-159`), so a zero-argument call reads
back. The only hazard is the *name*: `none` as a bare identifier would collide with the reader's
`unknownIdent` path if it ever appeared without parentheses, and `Effect`'s own `Option.none` is
a function call too, so `none()` is the faithful spelling. Recommend the wire name stay `none`
and the prelude re-export `Option.none`, which is what the printed image needs to type-check
against rc.112.

### 5.2 The list family: five atoms, not eight

| atom | arity | scheme | `eval` (through `Val.asList?`, §4.3) | TS prelude line | risk |
| --- | --- | --- | --- | --- | --- |
| `nil` | 0 | `mono [] (list never)` | `\| .nil, [] => some (.list [])` | `export const nil = (): ReadonlyArray<never> => []` | `sub (list never) (list t)` is true for every `t` by `sub`'s list arm (`Ty.lean:422`) and `never`'s (`:417`), so `nil` is assignable everywhere — checked by reading, worth a `#guard` |
| `cons` | 2 | `poly [var 0, list (var 0)] (list (var 0))` | `\| .cons, [x, xs] => (Val.asList? xs).map (fun vs => .list (x :: vs))` | `export const cons = <A>(x: A, xs: ReadonlyArray<A>): ReadonlyArray<A> => [x, ...xs]` | `inferJoin` widens: `cons(1, ["a"]) : list (nat\|string)`, which is TS's own answer |
| `get` | 2 | `poly [list (var 0), nat] (option (var 0))` | `\| .get, [xs, .nat i] => (Val.asList? xs).map (fun vs => match vs[i]? with \| some v => .some v \| none => .none)` | `export const get = <A>(xs: ReadonlyArray<A>, i: number): Option.Option<A> => Option.fromNullishOr(xs[i])` | `Option` answer keeps totality; `xs[i]` is `undefined` out of range on the host, so `fromNullishOr` is load-bearing and `Option.fromNullishOr` is the same function the KV row already uses (`prelude.ts:367`) |
| `length` | 1 | `poly [list (var 0)] nat` | `\| .length, [xs] => (Val.asList? xs).map (fun vs => .nat vs.length)` | `export const length = <A>(xs: ReadonlyArray<A>): number => xs.length` | the snapshot frame (§4.3); `List.length` lowers to `List.length` in OCaml (`Translate.lean:213`) |
| `append` | 2 | `poly [list (var 0), list (var 0)] (list (var 0))` | `\| .append, [xs, ys] => do let a ← Val.asList? xs; let b ← Val.asList? ys; some (.list (a ++ b))` | `export const append = <A>(xs: ReadonlyArray<A>, ys: ReadonlyArray<A>): ReadonlyArray<A> => [...xs, ...ys]` | `List.append` lowers to OCaml `@` (`Translate.lean:210`); O(n) on both, fine |

**Cut: `head`, `tail`, `isEmpty`.** Each is derivable in the term language as it will then stand:
`head xs = get xs 0`; `isEmpty xs = eq (length xs) 0` (`eq` already takes two naturals,
`Program/NativeAtom.lean:79-80`); `tail` is the only one that is *not* derivable — index-based
iteration with `get`/`length` over `iterate`'s cursor covers map, filter and fold without it, so
it is convenience, not expressiveness. The argument for adding them anyway is **print fidelity**,
and it is a real argument: an Effect program writes `xs[0]` or `Array.head(xs)`, and `get(xs, 0)`
prints further from the source than `head(xs)` does. Recommend: add them when a dogfood program's
printed form wants them, with the evidence attached, and not before. Every atom is a
`Spec` row, a soundness case, a prelude line, a profile row, and a golden — five places — and the
owner's standing question for any addition is "best abstraction? reuse?".

**Cut: `le`, `gt`.** `le a b = not (lt b a)`, `gt a b = lt b a`. Argument swapping is free in a
term language: the printer emits the nested calls, the checker types them, and nothing in the
inventory grows. If `le` is wanted for print fidelity later it costs one `Shape.natRel` row and
one `rfl` under §1.2's design, so deferring it is cheap to reverse. This is the clearest case in
the whole list where the brief's own list can shrink.

### 5.3 Strings: `concat` yes, `length` not yet

**`concat` is safe.** `String.append` lowers to OCaml `^` (`Translate.lean:205`), TS is `+`, and
Lean's `String.append` does no character traversal, so it stays clear of the axiom risk the tree
records. That risk is real and precisely documented: `Ty.key`'s docstring says a handle's target
is keyed by `String.toUTF8` because "`String.toList` and the string order reach
`Classical.choice` on this toolchain, so no member is ordered by its rendering"
(`Program/Ty.lean:120-123`), and `Program/Refs.lean:31-32` repeats it for `readRefName`. String
*equality* is already in the kernel path — `eq` at strings uses `==`
(`Machine/Term.lean`, `eval`'s second `.eq` arm) and `String.decEq` lowers to OCaml `=`
(`Translate.lean:204`) — so `concat` adds no new exposure.

| atom | arity | scheme | `eval` | TS prelude line | risk |
| --- | --- | --- | --- | --- | --- |
| `concat` | 2 | `mono [string, string] string` | `\| .concat, [.str a, .str b] => some (.str (a ++ b))` | `export const concat = (a: string, b: string): string => a + b` | none found |

**`strLength` should wait, and the reason is host agreement, not axioms.** Three faces, three
answers for the obvious spelling:

- Lean `String.length` counts `Char`s, i.e. Unicode scalar values.
- OCaml `lcnf_utf8_length` counts non-continuation bytes
  (`ocaml/gen/api_gen.ml:793`: `String.fold_left (fun n c -> if Char.code c land 192 = 128 then n else n + 1) 0 s`),
  which is also scalar values — so Lean and OCaml **agree**.
- TypeScript `s.length` counts UTF-16 code units, which **disagrees** with both on any character
  outside the BMP (an emoji counts 2).

So the atom is implementable and can be made to agree — the prelude line must be
`[...s].length` (JS spread iterates by code point), not `s.length` — but it is a
correctness trap with a silent failure mode, and it is worth landing on its own with a
differential test over a non-BMP fixture rather than inside a batch of twelve. Also: `String.length`
is closer to the `String.toList` path that `Ty.key` avoids than `String.append` is, so the
soundness proof for it should be checked against the axiom gate before the atom is committed, not
after. Recommend: defer, with this paragraph as the ticket.

### 5.4 The count

| family | add now | derive or defer |
| --- | --- | --- |
| option / selection | `ite`, `some`, `none` | — |
| arithmetic | `mul`, `sub`, `div`, `mod` | `le`, `gt` (derivable) |
| list | `nil`, `cons`, `get`, `length`, `append` | `head`, `tail`, `isEmpty` (two derivable, `tail` on print-fidelity evidence) |
| string | `concat` | `strLength` (host agreement, §5.3) |

**Twelve added, 32 atoms total.** Under §1.2's design the arithmetic four cost one `rfl` each
(all `Shape.nat2`), `ite`/`some`/`none`/`nil`/`concat` cost one short block each, and the four
list atoms cost one block each on top of the shared `hasTy_list_inv` — so the marginal proof cost
is roughly nine short blocks plus one inversion lemma, against the 17 full blocks a naive
extension of `nativeAtom_typed` (`Laws/Program/Typed.lean:586-749`, 165 lines for 20 atoms, so
about 8 lines an atom) would cost. That is the return on §1.2, stated honestly: it is a factor of
about two on the proof, and a factor of four or five on the *faces*, because the prelude and the
profile stop being separate hand edits.

## 6. Preserving the LCNF reification

### 6.1 It works today, and here is the evidence

`NativeAtom.eval` already compiles to OCaml with no hand code. Read at the generated file:

- `ocaml/engine/api_engine.ml:2808-2809` —
  `(* LCNF mono: Effect4.Program.NativeAtom.eval (x.1 : Effect4.Program.NativeAtom) (x.2 : List Effect4.Store.Val) : Option Effect4.Store.Val *)`
  followed by `let program_native_atom_eval (x_1 : native_atom) (x_2 : val_ list) : val_ option =`
  and a nested `match` that mirrors the Lean arms one for one (`:2819-2830` is the `succ` arm:
  `NativeAtom_succ -> match x_2 with | head :: tail -> match head with | Val_nat n -> …`).
- `:3115-3122` — `program_native_atom`, the name-keyed wrapper, lowered from `nativeAtom`.
- `:3124-3131` — `program_eval_term`, lowered from the `evalTerm`/`evalTerms` mutual block, with
  the environment read through the functor's `E.get`.
- `:867-886` — the `native_atom` OCaml variant, one constructor per Lean constructor.

The file's own header names the root set and the regeneration command
(`api_engine.ml:1-2`: `LcnfGen.lean --out ocaml/engine/api_engine.ml --import Effect4.Api --cap 2000
--externs ocaml/engine/externs.txt … Effect4.Machine.FnName.total Effect4.Machine.FnName.partialUpdate
Effect4.Machine.FnName.modify Effect4.Machine.FnName.modifySome …`). Two consequences:

1. **The four `FnName.*` roots in that list disappear with `FnName`.** They are explicit roots
   today because `refStep` reaches them through an extern row
   (`externs.txt:94`: `fn Effect4.Machine.refStep 2 sh_ref_step fn_name_total fn_name_partial_update fn_name_modify fn_name_modify_some`).
   After L4, `refStep` calls `evalTerm`, which is already in the import closure, so that extern
   row loses its four function arguments and the four roots come off the command line. That is a
   *simplification* of the engine seam, and it should be made in the same commit or the row goes
   stale — the generator refuses a stale row (`externs.txt:25-27`, deviation D4: "each is inlined
   or reached only through a row that deletes it, so a row would be a stale ledger and the
   generator refuses one (G10)").
2. **The owner's rule is satisfiable as stated** ("anything on the OCaml side not made directly
   from LCNF is ditched; keep only the pipeline's import closure"): a binder term inside a store
   operation keeps the whole atom semantics inside the LCNF closure, because `evalTerm` is already
   in it.

### 6.2 Which parts of my design keep the lowering, and which endanger it

**Keeps it.**

- `eval` as a `match` on the enum over `Val`, `Nat`, `Bool`, `String`. This is why §1.2 refuses a
  function field: the lowering above is a `match`, and a `Spec.eval : List Val → Option Val`
  field would make it a closure read out of a record, reached only through a partial application.
  LCNF's mono phase specializes what it can see; a closure in a table row is precisely what it
  cannot, and the failure mode is a `hole` in the generated file rather than an error.
- `Spec` as a record of `String`, `Option Nat`, `Bool` and `Scheme`. It is *metadata*: nothing in
  the run path reads it, because `typeOf` is compile-time only (`Program/NativeAtom.lean` is not
  in the engine's root set — the engine runs `Effect4.Api.run`, and typing is not on that path).
  So `Spec` can be as declarative as we like without touching the lowering at all. This is the
  single most useful thing to know about the design: **the typing half is free of LCNF
  constraints; only `eval` is constrained.**
- `Val.asList?` (§4.3) is a plain match plus `snapshot?`, both first-order.
- `Scheme.apply` calling `Ty.matchTemplate`: compile-time only, same reason.

**Endangers it.**

- A `Decidable` instance in `eval`'s path. `eval` uses `decide (a < b)` today for `lt`
  (`Machine/Term.lean`, `eval`'s `.lt` arm) and it lowers because `Nat.decLt` has a builtin row
  (`Translate.lean:158`). A new atom that decided something *without* a row — a `List` membership,
  a `Ty` comparison — would lower to the instance's own mono declaration, which may or may not be
  in the closure. Rule: every `decide` in `eval` must be on a `Nat`, `Bool`, `String` or `UInt8`
  comparison that `builtin?` names (`Translate.lean:154-230`).
- `Nat.mul`'s unclamped lowering (§4.2). Not a hole, worse: a silent wrap.
- Anything reaching `String.toList` or the string order — the `Classical.choice` risk of §5.3 is
  an *axiom-gate* risk, but the same functions are also the ones `builtin?` does not have rows
  for, so it is an LCNF risk too. `String.length` has a row (`:206`); `String.toList` does not.
- A typeclass-polymorphic helper in `eval` (a `Traversable`, a `BEq` on `Val`). `List.all` and
  `List.elem` already needed table fixes for their instance arguments
  (`ocaml/gen/NOTES.md:274-276`: "`List.elem`'s `BEq` instance is a relevant argument; `List.all`
  takes the list first — each found by `ocamlopt`, each a one-line table row"), which is the good
  news: the failure is a type error in `ocamlopt`, not a wrong answer. Still, prefer an explicit
  recursion or a `List` function with an existing row.

**How to know, cheaply, without running the Lean compiler.** The engine's own check is that the
functor body type-checks — `externs.txt:5-7`: "the table is complete iff api_engine.ml compiles".
So the verification for a new atom is `make gen-eff` then `cd ocaml && dune build`, and a hole or
a type error names the missing row. `make check-ocaml` (`Makefile:361-364`) runs it.

## Recommendations for the push

**Now, inside the current push, in this order.**

1. **L3a — the four atoms L4 is blocked on** (`ite`, `some`, `none`, `mul`), written into the
   existing `NativeAtom` shape (enum + `name`/`arity`/`eval` in `Machine/Term.lean`,
   `constGeneric`/`mono`/`typeOf` in `Program/NativeAtom.lean`), with `inferJoin` added to
   `Ty` and its one law (`inferJoin` is sound by the same guard: `matchTemplate_sound`'s proof
   is `unfold` + `aesop` and does not care which inference produced σ). Fix `Nat.mul`'s clamp in
   `Translate.lean:161` in the same commit. Four soundness cases by hand is cheaper than building
   the table first.
2. **The `atomSound` aesop rule set**, with `Fits.singleton_inv`, `Fits.pair_inv`,
   `Fits.all_sub_string`, `Val.hasTy_nat_inv`, `_bool_inv`, `_string_inv` as its rules. This is
   the instrument the chore has now asked for twice (20 atoms proved by hand, 12 more coming), and
   the owner's rule says build it on the second appearance. No named rule set exists in the tree
   yet, so this is also the precedent for the next one.
3. **L4's scope fix, in L4's own commit** (§3.5): `Signature.scopedOp`, the generated `perform`
   arm, and the red control `#guard Eff.scopedAt 1 (.perform (.refUpdate (.var 5)) (.var 0)) = false`.
   This is the one silent defect in the whole design and it must not be left for the faces to
   find.
4. **L4's printer/reader change**: `printRow` gains `n` and `Option Term`; `LambdaShape`/`atom?`
   retire; the reader uses the `ReadRefusal.binder` it already has. Close finding F3
   (`prelude.ts:24-30`) explicitly in the commit message — `Ref.modify` has been printing the
   wrong lambda shape and this fixes it.
5. **Correct the two stale documents** (`ocaml/gen/NOTES.md:255`,
   `ocaml/engine/externs.txt:157-162`): the division guard is in `Translate.builtin?` and has been
   for some time. Flip the two `fn?` rows to `fn` when `div`/`mod` land.

**After this push, as its own slice.**

6. **The `Spec` record and `Scheme`** (§1, §2), with `sound_of_mono`/`sound_of_shape`/`sound_of_poly`
   and `all` generated. Do it *after* the four atoms, not before: the four atoms tell you whether
   `Scheme.poly` + `inferJoin` is right, and the table is a refactor of a working thing rather
   than a speculative design. Land the `Spec.ts` field and the prelude generator group in the same
   slice, because that is where the table pays for itself.
7. **`Val.asList?` + `Val.hasTy_list_inv`, then the five list atoms** (§4.3, §5.2). The inversion
   lemma is the gate: write it first, with the snapshot counterexample of §4.3 as a `#guard` red
   control: `nativeAtom "length" [Effect4.Machine.Val.fibers [(0 : FiberId)]]` must be
   `some (.nat 1)`, not `none` (`Val.fibers` is the snapshot constructor,
   `Machine/Alphabets.lean:222-223`).
8. **`sub`, `div`, `mod`, `concat`** — one `Shape` row each under the table, or one short block
   each without it.
9. **Deferred with a reason**: `strLength` (three-face code-point agreement, §5.3), `head`/`tail`/
   `isEmpty` and `le`/`gt` (derivable; add on print-fidelity evidence from a dogfood program),
   `natBound` enforcement inside `evalTerm` (a profile question, not an atom question).

**What I did not resolve, and who owns it.** Whether the atom table should own its *own* TS
prelude text (§1.2's `Spec.ts`) or the prelude should stay a hand-written transcription with the
self-test as its guard is a taste call about where the faces live, and the file itself claims the
hand-written status deliberately (`prelude.ts:9-11`). I recommend generating it; the owner
decides. Second: whether `head`/`tail` earn their place on print fidelity alone is a judgement
about how close the printed image must sit to idiomatic Effect, which is the surface question the
authoring layer owns, not this note.

## References

**Papers and prior art.**

- J. C. Reynolds, *Definitional interpreters for higher-order programming languages* (1972) — the
  defunctionalization transformation. Why: it names what our atom table *is* (§3.1), which is the
  argument that no function value is needed rather than an excuse for not having one.
- GHC's `compiler/GHC/Builtin/primops.txt.pp` and `utils/genprimopcode` — one declarative file
  (name, type in a small DSL with type variables, arity, effect flags, docs) from which the
  datatype, the name table, the typing function and the manual are generated. Why: the closest
  working analogue to §1.2, including the lesson that the type column is a DSL.
- LLVM's `llvm/include/llvm/IR/Intrinsics.td` and `llvm-tblgen` — especially `LLVMMatchType<0>`.
  Why: it is `Ty.var` bound at first occurrence, independently arrived at (§2.1).
- Cranelift's `cranelift/codegen/meta` — a table in a different language from the compiler. Why:
  the negative lesson (§1.1); our table must stay in Lean so the exhaustiveness check is the
  proof.
- The WebAssembly core specification's instruction/opcode table and `call_indirect`/`funcref`.
  Why: `funcref` through a table index is defunctionalization in a spec, and it is the shape our
  "program as a `Val.ref` to its digest" would take if a function ever had to be stored
  (`docs/core/language-cut.md` §1).

**Lean APIs and project mechanisms.**

- `Ty.var`, `Ty.Subst`, `Ty.instantiate`, `Ty.infer`, `Ty.matchTemplate` —
  `src/Effect4/Program/Ty.lean:433-491`. Why: the scheme language already exists; §2 is reuse,
  not design.
- `matchTemplate_sound`, `instantiate_closed`, `infer_closed`, `rowTy_closed` —
  `src/Effect4/Laws/Program/Template.lean:47-84`. Why: the proof pattern (`aesop` with per-call
  rules) and the guarantee that a closed row types exactly as before.
- `Fits`, its five inversions, `nativeAtom_typed`, `evalTerm_hasTy`, `evalTerm_isSome` —
  `src/Effect4/Laws/Program/Typed.lean:341-415`, `:586-749`, `:770-879`. Why: the cost centre and
  the theorems every new atom must keep.
- `Var.name`, `printTerm`, `printRow` — `src/Effect4/Codegen/PrintLeaf.lean:152`, `:162-174`,
  `:265-279`; `Var.read`, `readTerm`, `ReadRefusal.binder`, `Var.name_inj` —
  `src/Effect4/Codegen/Read.lean:57-58`, `:103-107`, `:143-164`, `:1096-1132`. Why: levels, not
  indices — the answer to the capture question (§3.4).
- `Codegen/Forms.lean:17-73` (`ArgClass`, `TermTemplate.here`, `Template.expand`, `insert`). Why:
  the template table already speaks levels, so the lambda skeleton is one row.
- `Eff.scopedAt_perform` — `src/Effect4/Program/Scoped.lean:26`, `:120-121`. Why: the silent
  defect of §3.5.
- `OCaml5.Lcnf.Translate.builtin?` — `src/OCaml5/Lcnf/Translate.lean:154-230`. Why: the 50-row
  precedent for "a table as a Lean function", and the authority on what `eval` may use (§6.2).
- `E4_nat` — `ocaml/engine/e4_nat.ml:39-49`, `ocaml/engine/e4_nat.mli:9-40`. Why: the arithmetic
  profile of the engine face, with N2/N3 documented and tested.
- `ProfileData.natBound`, `admitsNat`, `rc112` — `src/Effect4/Program/Profile.lean:117-142`,
  applied at `src/Effect4/Program/HostBoundary.lean:61`. Why: the JS bound is already a profile
  row; `mul` makes it reachable (§4.2).
- `Test/Audit/AxiomGate.lean:47-55`, `:213-244`. Why: the exact token list and the `opaque`
  ruling, which no part of this design needs.
- `tools/Effect4Gen/manifest.json` (21 groups) and `tools/Effect4Gen/Rows.lean:31-70`. Why: the
  generator pattern — reflection over constructors, a table evaluated in `MetaM`, a new group is
  a manifest entry and no driver change.
- `tools/Tools/TsGen.lean:532-570` (`atomRows`, `atomJs`, `payload`). Why: the profile face is
  already a projection of `NativeAtom.all`; §1.2(d) extends it rather than replacing it.
- `harness/truth/prelude.ts` (the whole file, especially `:1-31`, `:24-30` finding F3,
  `:151-195` the self-test table). Why: the one face that is hand-written, and the bug binder
  terms fix.
- `ocaml/engine/api_engine.ml:867-886`, `:2808-2830`, `:3115-3131`; `ocaml/engine/externs.txt:1-50`,
  `:94`, `:157-162`. Why: the proof that `eval` and `evalTerm` already lower, and the extern rows
  that L4 changes.
