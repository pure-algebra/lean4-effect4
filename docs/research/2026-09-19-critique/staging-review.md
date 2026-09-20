# Critique audit: binding, stored behavior, and compilation

Read-only against main `6d2385cd` on 2026-09-19. No repository edit and no Lean invocation.
The root owns the Lean slot. The root reported executing
`lake env lean /private/tmp/effect4-critique-staging-probe.lean` successfully (exit 0).
The finite examples below therefore have kernel-checked `rfl` proofs; general composition
and semantic weakening laws remain proposed.

## Coordinator must know

The critique identifies useful boundaries but its category and staging account is not an
accurate description of this repository. Several mistakes repeat existing authoritative
prose in `docs/core/ontology.md` §5.4, which must be corrected along with the critique.
The economical repair is precise composition over the existing syntax and meanings,
using the existing weakening operation. Do not introduce a second syntax or a staging framework.

## 1. The actual binder semantics refute the advertised category operations

* `Machine/Term.lean:94-103,426-427`: variables are natural-number positions;
  `evalTerm env (.var i) = env[i]?`.
* `Program/Eff.lean:441-450`: positions are explicitly from the START of the environment,
  and insertion shifts every position at or above a fixed cut.
* `Program/Checker.lean:138-141`: `bind first rest` checks `rest` in
  `env ++ [first.answer]`. It joins errors with **Ty.join**, not raw `Ty.union`.
* `Laws/Program/Denote.lean:94,246-254`: successful bind evaluates `rest` under
  `env ++ [value]`, preserving the store of `first`, and short-circuits failure.

Consequences:

1. At `Γ ++ [A]`, the identity body is `.succeed (.var Γ.length)`, not `.var 0`
   unless Γ is empty. In `[bool,nat]`, `.var 0` has type bool and reads the bool.
2. Raw `.bind p q` does not compose `p : Γ,A → B` and `q : Γ,B → C`.
   Its `q` runs in Γ,A,B. It therefore sees the former A in B's expected slot.
   The zero-context example p=constant7 and q=var0, initial input4, returns4.
3. Raw reassociation is false even for pure, terminating, well-scoped programs.
   With p=constant1, f=constant2 and g=var0, `bind (bind p f) g` returns2;
   `bind p (bind f g)` returns1. The final body's context changed.
4. Positional naming is not scope safety by itself: `Term.var 0` is a legal raw
   Term at the empty environment, with `scoped 0=false` and `evalTerm []=none`.
   Safety belongs to the checking judgment and its soundness theorem.

### Exact reusable proposal

Keep `Eff` as the sole syntax. At fixed Γ define the *operation*, without a wrapper AST:

```
idAt Γ := Eff.succeed (Term.var Γ.length)
composeAt Γ p q := Eff.bind p (q.weaken Γ.length)
```

`q` originally sees Γ,B. The weakened copy sees Γ,A,B and ignores the inserted A.
Existing `Program/Fold.lean:3159-3171` supplies `Eff.weaken` through the generated
frontier algebra. Existing `Program/Typing.lean:152-155` proves its exact typing law:

```
effTy σ (pre ++ inserted :: post) (p.weaken pre.length)
  = effTy σ (pre ++ post) p
```

The exact typed composition statement is:

```
effTy σ (Γ ++ [A]) p = some ⟨B, E, R⟩ →
effTy σ (Γ ++ [B]) q = some ⟨C, F, S⟩ →
effTy σ (Γ ++ [A]) (composeAt Γ p q)
  = some ⟨C, Ty.join E F, R.union S⟩
```

`Laws/Program/Typing/Sound.lean:177-184` already supplies `effTy_bind` as the exact
Option equation; combine it with `effTy_weaken`, with no new checker or predicate.
`Program/Typing/Rules.lean:282-292` already proves the generic lookup insertion law
for any element type, privately. If a value-side proof needs it, expose/move that
one shared lemma at an appropriate lower import layer rather than independently
re-proving the same list arithmetic for typing, evaluation, printing and captured code.

The missing high-value semantic lemma is (start on Straight, then the appropriate
budget-independent Looped relation):

```
meaning (p.weaken pre.length) (pre ++ inserted :: post) s
  = meaning p (pre ++ post) s
```

The names `pre`, `post` in this semantic equation are value environments. The typing
lemma uses type environments. This is not yet a checked theorem; scope/fragment hypotheses
must be recorded at the selected meaning. Raw `meaning` currently has an outside-fragment
fallback, so a theorem over it must not be advertised as a full Eff semantic law.

First establish the shared term transport equations:

```
evalTerm (pre ++ inserted :: post) (t.weaken pre.length)
  = evalTerm (pre ++ post) t
evalTerms (pre ++ inserted :: post) (ts.weaken pre.length)
  = evalTerms (pre ++ post) ts
```

No new data carrier is needed. The existing evaluator and weakening are already folds
(`Program/Folds/Term.lean:24-27`). Derive the required compatibility with the existing
fold/induction machinery, then lift through Eff. Extend to a general renaming/substitution
operation only when a concrete consumer needs more than slot insertion.

Use this lemma plus `meaning_bind` once, then derive left/right identity and associativity
for `composeAt` **up to the selected denotational equality**. Quantify over all fitting
Γ environments, the input, and valid starting stores. Error-state retention is part of
that equality. At concurrent meaning, budget/ticks/guard boundaries can be visible; do not
silently carry the coarse straight-line equality to the scheduler observation.

The grading carrier should use existing normalized `CTy`/`ErrTy` or explicitly quotient
raw Ty by normalization. `Laws/Program/TypeAlgebra.lean:429-459` proves raw `join` commutative
and associative, but `join never t = normalize t`, not `t` for arbitrary raw Ty. Strict unit
laws on canonical types are at lines471-489. `Requirement.union` uses canonical Row union.

“Free algebra” uniqueness alone does not prove these sequencing laws. It says two folds
agree when their algebras agree; the algebra's composition laws and scope transport still
need proof. Likewise `sync` contains a Term, not a stored Lean `Val → Val` function, and
`select` is not by itself a proof of a premonoidal structure. Treat “graded Freyd category”
as a possible later characterization after these concrete laws, not a present theorem.

## 2. The displayed continuation definitions are fabricated

Actual `Laws/Program/InterpR.lean:43-57`:

```
ScopeFrame.resume (kind : GuardKind) (next : ExitV → RProgram)
ScopeFrame.answer (next : ExitV → RProgram)
ScopeFrame.restoreMask ... / asyncFinalizer ... / finalizerMask ... / iter ... / loop ...
RSaved := {current : RProgram, stack : List ScopeFrame,
           interruptible, interruptedCause, deferredInterrupt}
```

So RSaved is a RECORD, not just a list, and the semantic reference carrier intentionally
contains higher-order continuations. It lives in Laws. It is not canonical serialized
program content. The runtime carrier is `Machine/Frames.lean:307-318`'s `FrameFiber`, with
`current : Prim ...` and `stack : List (Prim ...)`, instantiated using first-order
`EffName` and `EffThunk`. `Program/Compile.lean:155-215` shows named continuations and
captured points. The interpreter's functions are separate parameters
(`Machine/Frames.lean:269-301`).

Do not “repair” the reference semantics by forbidding its functions. Keep the intentional
separation: higher-order semantic carrier, first-order runtime machine, and the relation
between them. First-order data makes codecs and replay possible; it does not automatically
prove whole-state serialization, storage migration invariants, or target memory safety.

## 3. Capture is first-order data; the issue is lifecycle and invocation policy

`Machine/Stores.lean:134-142` is data: path, env, fuel, tape, ctx and root. It violates no
no-function condition today. The issue is that it is a suspended runtime execution context,
not the right universal reusable code value. `Program/Compile.lean:80-88` deliberately
captures acquired value plus context for finalizers. `EffName.releaseUnder` at211-215
explicitly restores the captured context. Therefore “always use the caller's dynamic
context” is false as a universal policy, including a behavior already implemented here.

A code pointer plus `List Val` is a useful candidate, not a sufficient closed-code contract:

* Code identity must resolve to the same admitted root and signature; a hash by itself is
  not a mathematical proof of identity or admission.
* The entry must resolve by the existing `Node.at_` path scheme to an Eff body with a
  declared lexical type environment and an invocation argument/result type.
* `env` must fit that exact environment; a `List Val` alone is not typed.
* Captured handles require HandlesFit/world ownership and validity at invocation. They
  are runtime capabilities even though their representation is first-order.
* Invocation must separately specify lexical captures, services/context capture policy,
  scope/lifetime ownership, interrupt policy and dynamic budget/tape. Policies can differ
  between finalizers, resolver functions and caches.
* A persistent code package and a live instantiated closure need not have identical
  persistence rules. A live closure may refer to cells owned by a run; exporting it must
  either include an explicit reachable-world boundary or refuse those captures.

Start with a public contract of code resolution and typed invocation, reusing
`Node.at_`, Eff, Ty and the agreed world relation. Defer the `Val.codeRef` constructor and
its hash/path representation until a named consumer needs a storable behavior. No new
second program representation or universal closure carrier is necessary now.

## 4. compileEff and LCNF are distinct arrows, not Futamura stages

`Program/Compile.lean:345` defines `NCode := Prim EffName EffThunk Val ...`.
`Machine/Frames.lean:100-150` lists frame primitives: success/failure, sync/suspend,
onSuccess/onFailure/onExit, iterator/while/async. These are not ANF let/join/case instructions.

`compileEff : NativeEff → Point → NCode` (`Compile.lean:549-620`) consumes concrete env,
fuel, tape and completed-fiber information and constructs frame code. It does not call
the type checker. `.succeed (.var 0)` compiles to success3 under env[3] and success5 under
env[5]. Continuations resolve source paths and can compile more code when invoked. Calling
this a structural runtime compilation/elaboration is accurate; calling it an established
Futamura specializer is not.

The LCNF route instead reads compiled **Lean declarations**. `OCaml5/Lcnf/Dump.lean:36-41`
wraps `getMonoDecl? : Name → CoreM (Option (Decl .pure))`, not `NCode → LCNF`. The actual
translator now reads `Conform.Lcnf.persistedMonoIndex` directly to avoid the module export
filter (`Translate.lean:1012-1036`, `Tools/LcnfGen.lean:88-95`). Thus even the old
`getMonoDecl?` shorthand in lcnf-route needs care. The roots in LcnfGen are named Lean
machine functions. Their implementations, including interpreters if selected, are lowered;
a separate theorem is needed to claim specialization of any particular Eff program.

```
Eff data --compileEff at Point--> runtime frame data NCode
Lean implementations --Lean compiler--> stored mono LCNF declarations
stored mono LCNF --translateClosure--> Ml.Syntax --render--> OCaml source
```

The proof edges are different. A semantic theorem for Eff-to-frames does not prove the
Lean compiler, LCNF translator, source renderer or native execution. `Translate.localFun`
(lines880-892) emits local functions for join points; no native jump guarantee follows
from that source shape. A TypeScript trampoline is proposed work, not implemented by this
OCaml translator.

## 5. Literature checked, and what it does NOT imply

The official LMS tutorial defines `Rep[T]` as staged computation and plain T as a
staging-time value, and distinguishes `Rep[A] → Rep[B]` from `Rep[A → B]`. This informs
phase separation; it is not evidence that Effect4 already has LMS's type distinction.
[Official LMS tutorial](https://scala-lms.github.io/tutorials/start.html).

MetaOCaml CSP is not a ban on closures or dynamic values. Kiselyov's paper explicitly
explains sharing lifted values during in-process execution versus copying/serialization
when code is saved. The implementation account even describes pointers to functional
values. Effect4's first-order portability boundary is a deliberate stronger contract,
not a direct consequence of CSP.
[Kiselyov, Generating Code with Polymorphic let, §2.2](https://okmij.org/ftp/meta-programming/let-insertion.pdf),
[MetaOCaml implementation account](https://www.okmij.org/ftp/meta-programming/Quines.html).

Futamura's compiler-generation method concerns specializing an interpreter. In standard
projection notation, first: `mix(int, source) = target`; second:
`mix(mix, int) = compiler`; third: `mix(mix, mix) = compiler-generator`.
Translating LCNF to a target AST is not a second projection, and the critique mislabels
that as a compiler generator as well. No existing self-applicable specializer was found.
[Futamura's paper](https://www.jstage.jst.go.jp/article/jssst/21/5/21_5_343/_article/-char/en),
[Jones, Gomard, Sestoft, §4.3.2](https://www.cs.utexas.edu/~novak/jonesgomardsestoft.pdf).

## 6. Related ontology claim to repair

`ontology.md:194-197` says replay theorems imply each reachable machine state is the image
of a unique command word. Actual `Laws/Api/Runner.lean:155-165`'s `replay_unique` proves
uniqueness of an action/homomorphism given empty/single/append behavior. It does not prove
injectivity of journals into machine states. `Laws/Run.lean:161-165` reconstructs a reached
Run including its journal, under its fixed opening parameters. These are useful exact
statements; the unique-word gloss and “Machine cannot be data” conclusion are unwarranted.

## Proposed immediate work, in order

1. Execute the small concrete binding/compilation probes, correct ontology §5.4, and state
   the exact meaning selected for composition.
2. Reuse `Eff.weaken`/`effTy_weaken`; prove semantic weakening once, then derive typed
   composition and its semantic laws. Keep grades canonical.
3. Define deferred behavior contracts in terms of code resolution, typed lexical captures
   and named invocation policy. No executable stub or Val constructor until consumed.
4. Correct the pipeline map and keep each compilation relation's assumptions explicit.
   No Futamura implementation, new gate or fresh intermediate program representation.
