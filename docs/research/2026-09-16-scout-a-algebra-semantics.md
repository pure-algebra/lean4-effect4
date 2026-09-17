# Scout A: the semantics of the algebraic structure

Read-only seat, 2026-09-16, at `7556ddef` on `refactor/phase1-phase3`. I ran no `lake` and no
`make`. Nothing changed except this file.

Evidence words, used exactly. **Read** means I read the source in this session and cite it as
`path:line`. **Recalled** means literature from my own knowledge, unfetched here. **Assumed**
means taken from the brief without checking. Nothing here is **proved** or **tested** by me,
because I ran no compiler; "the theorem is present" means the declaration and its proof script
are in the file I cite. That `lean4-doc` builds with green guards is **assumed**; I read all 675
of its Lean lines and checked one guard's span arithmetic by hand.

Read in full: the design note (412 lines, including the §12 added mid-session); the named
sections of the precedents note; all five Lean files of `/Users/pooks/Dev/lean4-doc`;
`.lake/packages/effects/Effects/Algebra/` and `Family.lean`; `tools/Effect4Gen/Fold.lean` and the
relevant emitted blocks of `src/Effect4/Program/Fold.lean`; `src/Effect4/Codegen/Forms.lean`;
`tools/Effect4Gen/binders.json`; the printer's head clauses, `readable`, `LawfulSpelling`,
`LawfulTable`; `.lake/packages/typescript/TypeScript/Render.lean`; `Schema/Annotations.lean` and
`Representation`'s constructor list; Lean core's `Init/Data/Format/Basic.lean`.

---

## Q1. Is `Doc A` with its own algebra the right object?

**Verdict: right object. `Effects` is not a candidate at all. The hand-written eight-constructor
algebra is honest today and is a duplication that should be closed inside S1 or S2.**

**What `Effects` offers**, enumerated, not sampled. `Signature` as `{Op, Answer : Op → Type}`
(`Algebra/Signature.lean:30`) with `Signature.sum` (`:35`); `Program signature A | pure | vis
(operation) (next : Answer operation → Program …)` (`Algebra/Program.lean:33`), a free monad whose
continuations are **Lean functions**, and whose own docstring says it "intentionally has no
decidable equality, serialization, or content identity" (`Algebra/Program.lean:9`); `Handler` and
`interpret` (`Algebra/Handler.lean:30`, `:45`); the monad, interpretation and signature-sum laws
(`Algebra/Laws.lean`, `Algebra/Sum.lean`); the universal property (`Algebra/Universal.lean:98`,
`:119`, `:214`); `Family` and `Alphabet` (`Effects/Family.lean:22`, `:63`).

What it does **not** have: no container, no polynomial functor, no `W`-type, no generic
first-order signature with an initial algebra, no `cata`, no algebra map, no fusion. I grepped
`Container`, `Polynomial`, `WType`, `cata`, `initial` across `Effects/` and the only hits are the
three declarations with "initial" in their names. So nothing there is reusable for a first-order
inductive. Encoding `Doc` as a `Program` trades away `DecidableEq` (`Doc/Core.lean:34`) and with
it every `#guard` in `DocTest/Guards.lean`. Same objection the precedents note raises against
reusing `Effects.Program` as the syntax carrier (§14.7).

**Generated, or hand-written?** `tools/Effect4Gen/Fold.lean` reads the environment by reflection
(`getConstInfoInduct` at `:44`, argument types by `forallBoundedTelescope` at `:60`) and emits per
block: `XFam`, `XAlgebra`, `cata_X`, `XHom`, `hom_eq_cata_X`, `XAlgebra.id`, `cata_id_X`,
`foldMap_X`, `foldMapAt_X`, `XMAlgebra` with `foldM_X`, `foldM_eq_cata_X`, `foldM_natural_X`, and
a frontier family (`:392`). Six of the eight declarations in `Doc/Core.lean` are exactly what it
emits for a single-family, non-parameterised inductive.

The two that are **not** generated are the two the package actually uses: `AlgMap`
(`Doc/Core.lean:108`) and `cata_fusion` (`:120`). I grepped `src/` and `tools/` for `AlgMap`,
`cata_fusion`, `_fusion`: no hits. Yet the repository needs fusion in at least three places and
does each by hand, `weaken_eq_cata_eff` (`src/Effect4/Program/Fold.lean:3177`) being the clearest.

**Recommendation:** add `AlgMap` and `cata_X_fusion` to the generator and regenerate
`Fold.lean`; keep `Doc/Core.lean` hand-written with a header naming the generator rows it mirrors.
Do not invert the dependency so `lean4-doc` consumes this repository's meta code; its lakefile
says "No dependencies" and that is worth more than removing 60 mirrored lines.

**Where I disagree with the design.** §2's P5 bullet says "`Doc ann` with a product `Measure`".
There are **two** measures and only one is a `Doc`-fold: `Info` (`Doc/Core.lean:157`, folded by
`infoAlg` at `:163`) and `Measure` (`Doc/Measure.lean:16`, folded over the **stream** at
`Doc/Layout.lean:114`). §9 law 4 ("`measure (cat a b) = measure a <> measure b`") is a document
statement; what is present is `measure_append` on streams (`Doc/Laws.lean:66`). The document
statement holds for the house policy and fails for the elastic one, whose second operand starts at
a different column. Restate law 4 as the stream law plus a house corollary.

---

## Q2. The policy as a zygomorphism

**Verdict: yes, standard, and `layout_info` is the right agreement theorem. What is lost against a
paramorphism is precisely what Wadler and Bernardy need.**

A zygomorphism (Fokkinga; recalled) pairs an auxiliary algebra `aux : F A → A` with a main algebra
on `A × B` whose second component may read the auxiliary results of the immediate subterms.
`layoutAlg` (`Doc/Layout.lean:44`) is that shape exactly: every field's first component is
`infoAlg`'s operation on the first components (`:45` to `:58`), and the second reads `f.1`/`w.1`
in one place, `choice` (`:54`).

The name matters. Banana-split is for two **independent** algebras,
`⟨cata f, cata g⟩ = cata ⟨f ∘ F fst, g ∘ F snd⟩`. Here the second component depends on the first,
so banana-split does not apply and only the `fst` half survives. `layout_info`
(`Doc/Layout.lean:87`) is that surviving half, proved by `cata_fusion` along `Prod.fst`
(`infoOfLayout`, `:76`), which is the defining property of the zygomorphism and the right
agreement theorem. Design §7 calls the pair "the banana-split/tupling law"; wrong name for a
dependent second component.

**What is lost against a paramorphism.** A paramorphism hands the algebra the subterms themselves,
so a policy could lay an alternative out again at a different column. The zygomorphism restricts a
policy to `Info = (breaks, hard, width)` (`Doc/Core.lean:157`), which is exactly what limits
`elastic` (`Doc/Layout.lean:99`) to `!f.hard && col + f.width ≤ width`. **That is not Wadler's
`fits`**: Wadler asks whether the flat alternative plus the text following it on the same line
fits, which needs the continuation, not the subterm. So neither zygo nor para suffices for Wadler
or Bernardy; that carrier is a function of the trailing document, which is what Lean core's `be`
implements as a work list (`…/lean4---v4.33.1/src/lean/Init/Data/Format/Basic.lean:252`). The
package's own docstring is honest ("the local form of Wadler's `fits`", `Doc/Layout.lean:16`); the
design document is not.

**Consequence for the design.** `Policy` (`Doc/Layout.lean:37`:
`flat : (width col : Nat) → (flat wide : Info) → Bool`) can express only greedy, lookahead-free
policies. Design §7's "the elastic one keeps a Pareto frontier of measures" is not supported by
this type and cannot be without changing the carrier. Rename `elastic` and record the optimal
policy as future work with a different carrier, or change `Policy` now, before the layout
specification's Lean API is built on it.

**One smaller loss.** `infoAlg.choice` sets `width := f.width` (`Doc/Core.lean:170`), the flat
alternative's own *flat* width, exact only when `flatten f = f`. That holds for
`group d = choice (flatten d) d` (`:141`) and fails for hand-built choices such as `DocTest.object`
(`Guards.lean:23`), whose inline branch may contain choices. Make `group` the only public
constructor, or add a decidable `isFlat` and state `elastic`'s faithfulness under it.

---

## Q3. The house policy, byte determinism, and the fusion lemma

**(a) Is the pair of house lemmas the right statement? Half of it, and §9 law 6 is misstated.**
`layoutAlg_house_width` (`Doc/Laws.lean:110`) is `rfl`: the algebra does not read the width.
`layout_house_stream` (`:115`) is by induction: the stream does not read the column. Together: the
house stream is a function of the document **and the indentation `i`**. Law 6 says "a function of
the document alone", which is false: `i` is threaded by `nest` (`Doc/Layout.lean:53`) and emitted
by `line` and `hardline` (`:47`, `:48`). Missing, and one line, is the corollary the goldens rely
on: `render` (`:102`) fixes `width = i = col = 0`, so `string (render d)` is a function of `d`.
Add it as the stated determinism receipt.

**(b) Is `lines_house` the right bridge to `containsNewline`? Shape right, two real caveats.**
The old renderer's only child-dependent decision is `containsNewline` (`Render.lean:114`) on
already-rendered children at three sites (`:135`, `:158`, `:186`); `lines_house`
(`Doc/Laws.lean:137`) turns it into `hasBreakHouse` on the child's document, which is the move
that makes the renderer a fold instead of a traversal over strings.

*Caveat 1, the most serious defect I found.* `lines_house` is about `(measure stream).lines`, and
`Measure.ofText` **defines** `lines := 0` for every string (`Doc/Measure.lean:59`), with
`lines_ofText` by `rfl` (`:70`). So `Doc.text "a\nb"` has `lines = 0` while its layout's text
contains a newline, and `spans`, `locate` and every byte offset downstream are wrong for that
document. The precondition lives only in a docstring (`Doc/Measure.lean:57`). This matters because
the old renderer does emit raw newlines inside strings: `.generator` writes `"function* () {\n"`
(`Render.lean:206`) and `docBlock` writes `"/** …\n"` (`:289`). A correct port turns those into
`hardline`s, but nothing in the type stops a future template from doing otherwise. Fix: make
`Doc.text` a smart constructor that splits on `'\n'` into `text`/`hardline` with the raw
constructor private, or add a decidable `WellFormed` and guard it.

*Caveat 2.* `containsNewline` is applied to `field.2`, the rendered value, not to
`name ++ ": " ++ value` (`Render.lean:135`), while the `Doc` choice is over the whole object
including the names. They agree because names are newline-free text, but that is a lemma about the
encoding, not an instance of `lines_house`. Put it in the S2 packet or the first attempt will
expect `rfl`.

**(c) Will `string ∘ render_house = Render.expr` come out of `cata_fusion`? No.** `cata_fusion`
(`Doc/Core.lean:120`) is fusion for the **`Doc`** signature: two `Doc`-folds. The wanted equation
relates an `Expr`-fold (`Render.expr`, `Render.lean:122`) with the composite of an `Expr`-fold
into `Doc` and a `Doc`-fold into `String`. The tool is initiality of `Expr`, and
`lean4-typescript` has no algebra at all: I grepped the package for `cata` and `Algebra` and found
nothing. S2 must generate one for `TypeScript.Expr`/`Stmt` or do about twenty cases by hand.

**Does `depth` force an exponential carrier? Not in the `Doc`.** `indentOf style depth` is
`style.indent * depth` spaces (`Render.lean:26`), and every use of `depth` in `expr`/`stmt` is
either unchanged or `depth + 1` at a block boundary (`:206`, `:228`-`:286`). That is `nest
style.indent`, and the `Doc` layout carrier already takes `i` (`Doc/Layout.lean:41`). What it does
mean is that the fusion statement is quantified in the depth:

```
∀ depth, Render.expr style depth e
       = string (layout house 0 (style.indent * depth) 0 (renderDoc e)).1
```

so the old renderer's own carrier is `Nat → String`, an inherited attribute and therefore an
exponential carrier, exactly as the estate ruled when it rejected `cata_ctx` (`docs/STATE.md`).
That is fine because the exponential is on the old side and dies with it, but the lemma must carry
the `∀ depth`; at `depth = 0` the induction does not go through.

**One encoding detail S2 will hit.** `stmts` (`Render.lean:275`) puts the indent *before* each
statement and a newline *after* each including the last, and the caller then writes
`indentOf style depth ++ "}"` (`:206`). The byte-identical `Doc` shape is
`text "{" ++ nest k (⋯ hardline ++ stmt ⋯) ++ hardline ++ text "}"`, not the obvious
`hardline`-separated join. Getting it wrong moves every golden by whitespace.

---

## Q4. Templates as the free monad over the syntax signature

**(a) The condition is right, with one correction that changes how law 9 is written: it is
decidable only when `Op` is finite and enumerated.** `print` is parameterised by `Signature Op`
(`Codegen/Print.lean:317`; `Signature` at `Program/Typing.lean:53`) and `printRow` reads
`sig.rowOf op` (`Print.lean:267`), so the row part of the table is a **parameter**, not data. The
estate's statement of exactly this property is `LawfulSpelling` (`Codegen/Read.lean:894`), a
`Prop` with seven `∀ op` clauses. The decidable version exists only natively: `LawfulTable` is a
`Bool` over a `RowTable` (`Read.lean:2925`), discharged `by decide` in `read_print_native`
(`:3050`) and `read_exact_native` (`:3064`). So §9 law 9 "by `decide`" is true at the native table
and is a hypothesis in general. Write the law twice or the first proof attempt stalls on an
arbitrary `Op`.

**(b) Characterise the image as a decidable predicate on trees, not on programs.** The ambiguity
is concrete: `suspend body`, `branch test a b` and `whileLoop i t s b` all print under
`Effect.suspend` (`Print.lean:333`, `:353`, `:356`). What separates them is the arrow argument's
shape: a bare body, a `.cond`, or an `.arrowBlock` whose first statement is a `letInit`. So define
`InImage : Tree → Bool` as the union of the template heads with their discriminating first
argument, and prove (1) `print e = ok t → InImage t` by induction on `e`, small; (2) pairwise
disjointness on trees satisfying `InImage`, by `decide` over the finite table crossed with the
finite classifier alphabet.

*Where I disagree with the design.* §3 says the overlap "is resolved by a deterministic
tie-break". A tie-break without (2) is a convention, not a justification: `read (print e) = ok e`
would still hold while `print (read x) = ok x` silently fails off the image. The second theorem is
the one needing `InImage`, and the estate already has it in its strong form: `read_exact`
(`Read.lean:2908`) has **no** `readable` premise. Do not lose that when the reader is regenerated.
`readable` (`Read.lean:779`) stays as the source-side half, and its clauses are already the ones
making the ambiguity unreachable (`yieldError` excluded at `:782`, because it prints as
`Effect.fail`, `Print.lean:323`).

**(c) The two theorems about the generic matcher.** With `unTmpl : Tree ⇀ (Ctor × Classifier ×
List Tree)`:

- *Section.* `∀ c k args, unTmpl (tmpl c k args) = some (c, k, args)`. One `rfl` per row,
  generated. This is design law 10 and it is cheap.
- *Retraction on the image.* `∀ t, InImage t → ∃ c k args, unTmpl t = some (c,k,args) ∧
  tmpl c k args = t`. The disjointness content, and the work.
- `read (print e) = ok e` for `readable e` is then induction using the section;
  `print (read t) = ok t` for `InImage t` is induction using the retraction.

The Narcissus framing of §4 is right for the *host* agreement and I agree with it. It buys "the
TypeScript reader agrees with the Lean reader" as a corollary of unambiguity. It does not buy the
Lean round trip, which still needs both of the above.

**(d) No second-order signature.** `Forms.Template.argument (slot cutOffset insertions)`
(`Codegen/Forms.lean:31`) is the right first-order encoding, implemented by `insert (n + offset)
count` (`:61`, `:56`), which iterates `Eff.weaken`. Against the binder table:
`tools/Effect4Gen/binders.json:29` gives `whileLoop` as `"slots": ["cursor","answer"],
"args": [[],[0],[0,1],[0]]`. The two are inverse views of one table (which of a constructor's own
binders an argument sees, versus how far to shift an argument inserted under new binders), so
generating the template's binder columns from `binders.json` is right.

*The caveat the design misses.* `Forms.Template` is over the **`Eff` signature**:
`Template.expand` returns `Eff NativeOp` (`Forms.lean:61`). So `Forms.all` (`:84`) is a
*source-side* table (derived TypeScript forms expanded into core `Eff`) and the design's table is
*target-side* (`Eff` constructor into `Tree`). §3's "`Forms.all` is already this shape and becomes
rows of the same table" is true of the **shape** (a first-order term with numbered holes carrying
a cut and an insertion count) and false of the **signature**. Two tables over two signatures with
one template calculus. Say so, or S4 attempts a merge and finds the type error late. The per-row
guard is the model to copy: `Forms.lean:198` is
`#guard all.all (fun f => [0,1,2,5].all f.checkExample)`, and `checkExample` (`:192`) is a full
round trip through the real printer and reader.

---

## Q5. `Fmt` as the correctness statement

**Verdict: well-posed after one repair; three Lean theorems and two host checks.**

As written in §4, "`Fmt e s` holds when `s = text (layout house (render (print e)))`" makes `Fmt`
the graph of a partial function, so "functional on the image" is trivially true and the theorem is
vacuous. What is wanted is injectivity in the other argument. Define `Fmt` relationally, as the
precedents note does (§8): `Fmt = { (e,s) | ∃ t, Tmpl e t ∧ Render t s }`, with unambiguity as
`(e,s) ∈ Fmt → (e',s) ∈ Fmt → readable e → readable e' → e = e'`. Define the relations first and
derive the functions; that is the whole point of the Narcissus shape.

Proved in Lean: (1) `Tmpl` unambiguous on the image, the retraction of Q4(c); (2) `Render`
injective on `InImage` trees, which is the genuinely new obligation (our renderer emits no
parentheses and needs none, and the house layout conflates no two distinct trees) and which I
would scope to the fragment the templates use rather than all of `Tree`; (3)
`print e = ok s → (e,s) ∈ Fmt` and `read t = ok e → (e, render t) ∈ Fmt`, both by construction.

Executed on the host, not provable in Lean: (4) the host parser inverts `Render` on the image
modulo `skipOuterExpressions`, a property of `tsgo`; (5) a host reader from the exported table
agrees with the Lean reader. By 1 and 2 this *would* be a corollary if the host reader could be
proved to land in `Fmt`, and it cannot, because it is TypeScript. What the relation buys is that
the check becomes `read_ts (parse s) = read_lean (parse s)` on one tree rather than a 408-program
string comparison.

Design §9 lists item 14 as one theorem. It is two, and renderer injectivity is the expensive one.

---

## Q6. The grammar annotation as a schema annotation

**Verdict: lawfully encodable, yes. "A schema declares its own concrete syntax" does not hold up;
the template belongs beside the schema with a reference from it.**

**Encodability.** `AnnotationKey A` needs `encode : A → Json`, `decode : Json → Option A`
(`Schema/Annotations.lean:25`), and `Lawful` needs both `decode (encode v) = some v` and
`decode raw = some v → encode v = raw` (`:33`). The second is strict: the decoder must reject every
non-canonical spelling. For a first-order template inductive with `DecidableEq`, a tagged encoding
with a strict field-order check satisfies it. One real implementation risk: the natural JSON
decoder that tolerates unknown or reordered fields breaks `encode_decode` at once, and the failure
will look like a proof problem rather than a decoder problem.

**The meta API.** `Representation` carries `annotations` on every constructor
(`Schema/Representation.lean:718` onward), so it fits structurally. Two objections. First,
`Representation` is by its own docstring the **pinned model of Effect's persisted schema
representation** (`:16`); putting our template inside it means the persisted JSON we emit and the
host validates carries a key Effect's runtime does not know, and every pin, digest and parity
check over that model moves. The design does not price this. Second, and structurally decisive:
the templates are indexed by `(Eff constructor, classifier)`, and a classifier is a predicate on
non-recursive arguments (`Print.lean:342` for `catchIf`, `:406` for `provideLayer`, `:267` for the
row shapes). A constructor corresponds to a member of a tagged union in the generated schema, so
an annotation could hang there; **a classifier is not a shape and has nowhere to hang at all.**

So keep the template table as its own P2 document keyed by `(constructor, classifier)`, and put on
the schema node an annotation carrying only a *reference* to the template key. The pinned
representation stays clean, the classifier gets a home, and the lawful-key obligation reduces to a
string. The slogan survives as "a schema node names its grammar row".

**A factual correction.** §3 says "`documentExpr` becomes rows of a second table" and §6.2 speaks
of `Schema.Struct`, `TaggedStruct`, `Class`, unions and `suspend`. `documentExpr`
(`Codegen/Schema.lean:374`) prints the **persisted JSON literal** of a document, not Effect Schema
combinator calls; I grepped `src/Effect4/Codegen/` for `Schema.Struct` and its siblings and found
none. Two different printers, only the first exists. S7 is two stages, not one.

---

## Q7. The proof graph, checked

**P1 existing.** All present and cited correctly: `hom_eq_cata_eff` (`Program/Fold.lean:1178`),
`cata_id_eff` (`:1423`), `weaken_eq_cata_eff` (`:3177`), `foldMapAt_eff` (`:1654`),
`EffAlgebra.id` (`:1354`), `frontierMap` (`:3054`), `read_print` (`Read.lean:1750`), `read_exact`
(`:2908`). No correction. **P2/P3 existing.** `decodeEntry_entry` (`Annotations.lean:57`),
`entry_of_decodeEntry` (`:66`). No correction.

**P5, laws 1 to 6.**

1. *Not proved as stated, and the statement should change.* `Doc` is genuinely not a monoid as a
   tree (`cat empty a ≠ a` syntactically). What is proved is that *layout* is associative and
   unital (`Doc/Laws.lean:43`, `:47`, `:51`), which is the right thing. Reword.
2. `layout_nest_nest`, `layout_nest_cat` (`:57`, `:61`). Present. `nest i empty = empty` under
   layout is missing and trivial.
3. Present as eight `rfl` simp lemmas (`Doc/Core.lean:143`-`:150`). Cheap.
4. Present on streams (`Doc/Laws.lean:66`), absent on documents. See Q1.
5. **Half present.** `layout_bracketed` (`:87`) proves bracketing; containment is not proved, and
   `locate` silently depends on it. `locate` is `find?` over closing order (`Doc/Layout.lean:150`)
   and returns the innermost span only if closing order is a linear extension of containment.
   Without that, `locate` is a heuristic. Prove `spans_disjoint_or_nested` and `locate_innermost`.
6. Present but misstated. See Q3(a).

**P4, laws 7 and 8.** Nothing exists; both are `#guard`/`rfl` over a table that does not exist
yet. Cheap once it lands. Law 7's real cost is the importer, not the guard.

**Printer and reader, 9 to 14.** 9: split into a `Prop` and a `decide`d native instance; cheap
natively, a hypothesis in general. 10: cheap, generated. 11: moderate, and it replaces not just
`Read.lean:1750` but the whole `read_print_*` family (`:1679`, `:1940`, `:1986`, `:2001`, `:2049`,
`:2064`), more than the design's accounting suggests. 12: expensive, needs `InImage` and the
retraction, replaces `read_exact` plus `read_exact_all` (`:2308`). 13: moderate, and **not by
`cata_fusion`** (Q3(c)). 14: the hard one, and it is two theorems (Q5).

**Missing from the graph entirely.** (i) `InImage` and `print e = ok t → InImage t`; laws 12 and
14 both rest on it. (ii) Renderer injectivity, stated separately from 14. (iii) `Doc`
well-formedness, no newline inside `text` (Q3(b)). (iv) `locate`'s containment theorem. (v) The
agreement between the template table's binder columns and `binders.json`/`Node.binders`. The
design says generation makes drift impossible; generation is not a theorem, and the estate's own
model here is the per-row guard (`Forms.lean:198`). Add the guard.

**Should be executed checks.** Law 13 is only needed while the old renderer exists; if S2 lands
the goldens byte-identical the golden diff is the receipt. The design says this at S2 and then
lists 13 as a theorem. Pick one. I would still prove it, because it is the only thing carrying the
old renderer's 408-program evidence onto the new one, but I would not block S2 on it. Law 7 and
the span agreement are checks, which the design says.

**Axiom ceiling.** `[propext, Quot.sound]` is right and the first pass is consistent: every proof
in `Doc/Laws.lean` is `induction`, `simp only`, `omega` or `rfl`, and `Doc/Core.lean` has no
`Classical`. Two cautions from the estate's record. Use `decide +kernel` for the table properties
(7 and 9); plain `decide` has pulled in `Classical.choice` here before. And
`Measure.append_assoc` (`Doc/Measure.lean:41`) closes with `repeat' split; all_goals omega`, fine
now and exactly the proof that starts pulling in instances if `Measure` gains a non-decidable
field. Design §7 flags `VisualConfig.terminalAspectScale : Float` as that hazard; the same rule
applies to `Measure`.

---

## Q8. Scouting S2

**What S2 needs.** (1) An **importer** in `Tools` turning the chosen source into a P2 document
with a pinned digest; the only new machinery, and a driver, not a model. (2) A decision on `Kind`
and `Field`: generated Lean inductives (structural equality, `#guard` decides) or `String` with a
validity predicate. I recommend inductives; 324 rows is past hand-writing and well inside
generation, and `String` kinds turn every typed view into a runtime check. (3) **Multiplicity per
field**; without it `Tree` cannot be validated and the typed views cannot be total. (4) **A path
convention by named field plus index, never by child ordinal.** The precedents note tested this
(finding 9): `forEachChild` flattens optional fields and type arguments into one stream, so
ordinals are not stable under an absent optional. The design states the convention for the parse
interchange (§3) but not for the model's own `Path`. Most consequential S2 decision. (5) The three
normalisations of precedents §12(c): qualified identifiers into a property-access chain, generic
calls into one call node with `typeArguments`, and the parenthesis lemma.

**TypeScript's table versus tree-sitter's.** TypeScript's is abstract, in lockstep with the
checker we already run, and lives in a `.d.ts`, so the importer walks declarations rather than
reading JSON; its kinds include token kinds and a long tail we never emit, so the table needs a
subsetting step and *the subset* is what gets pinned; its field names are compiler property names,
stable in practice, not a published contract. tree-sitter's is concrete, so it includes
punctuation and grouping nodes and models the surface; it is trivial to read and its multiplicity
data is explicit, which is better data; it is stale (precedents finding 10) and does not line up
with the checker.

What actually breaks with the concrete table: every template grows parenthesis and punctuation
nodes, so disjointness is decided over a larger alphabet and `InImage` must exclude parenthesised
spellings, a cost landing on the most expensive theorem. What breaks with the abstract table: a
host reader for *foreign* code cannot use it, because `tsgo`'s AST exists only after `tsgo`
parses. So the design's recommendation is right, and the reason is sharper than the design gives
it: **the abstract table for the image, because the image carries the expensive theorems; a
concrete table only for foreign code, where the obligation is a check, not a theorem.**

**The smallest `Tree` and `Tm` I would write.**

```lean
/-- Multiplicity of a field in the syntax table. -/
inductive Mult | one | opt | many
deriving DecidableEq, Repr

/-- The imported syntax table: each kind's fields in declaration order with their
multiplicity. `Kind` and `Field` are generated from the table so equality is structural
and `#guard` decides. -/
structure Sig (Kind Field : Type) where
  fields : Kind → List (Field × Mult)

/-- A term over the syntax signature with holes labelled in `X`. First-order on purpose:
`DecidableEq` whenever `X` has it, and canonical bytes. `Tm Kind Field Empty` is the tree. -/
inductive Tm (Kind Field X : Type)
  | hole (x : X)
  | node (kind : Kind) (children : List (Field × List (Tm Kind Field X)))
  | token (kind : Kind) (text : String)
deriving DecidableEq, Repr

abbrev Tree (Kind Field : Type) := Tm Kind Field Empty

/-- A hole in a template: which argument fills it, where the new binders cut into the
context, and how many there are. The de Bruijn shadow of a second-order metavariable of
arity `insertions`; the columns are generated from `binders.json`. -/
structure Slot where
  argument : Nat
  cut : Nat
  insertions : Nat
deriving DecidableEq, Repr

abbrev Template (Kind Field : Type) := Tm Kind Field Slot

/-- Substitution: the free monad's bind. -/
def Tm.bind {Kind Field X Y} (f : X → Tm Kind Field Y) :
    Tm Kind Field X → Tm Kind Field Y
  | .hole x => f x
  | .token k s => .token k s
  | .node k cs => .node k (cs.map fun (fd, ts) => (fd, ts.map (Tm.bind f)))

/-- Validity against the table: every field declared, in order, with its multiplicity. -/
def Tm.wellFormed {Kind Field X} [BEq Field] (sig : Sig Kind Field)
    (fits : Mult → Nat → Bool) : Tm Kind Field X → Bool
  | .hole _ => true
  | .token _ _ => true
  | .node k cs =>
    (cs.map (·.1) == (sig.fields k).map (·.1)) &&
    (cs.zip (sig.fields k)).all (fun (c, f) =>
      fits f.2 c.2.length && c.2.all (Tm.wellFormed sig fits))
```

About fifty lines plus the two monad laws (`bind .hole` is the identity; `bind` composes). Three
choices I would defend: children grouped by field, so paths are by name; `token` separate from
`node`, so a leaf carries text without inventing a field; and `wellFormed` a `Bool` against the
imported table rather than a dependent index, so the table can change without re-typing every
tree. The dependent alternative (index `Tm` by its kind) makes the typed views free and makes the
importer's output a type-level object, which is the same inherited-attribute trap the estate
rejected with `cata_ctx`.

---

## Q9. The effectful, typed compilation API

**(a) "Compile = pure fold producing an effectful plan" is right, and the alternative is not
available.** The decisive fact: `Eff` is not a Lean `Monad`. `Eff.bind (first rest : Eff Op)`
(`Program/Eff.lean:314`) takes a *program* as its continuation, not a function, because the answer
is a de Bruijn variable. There is therefore no `Monad (Eff CompileOp)` instance, and `foldM_eff`
(`Program/Fold.lean:2337`), which requires `[Monad M]`, **cannot be instantiated at
`M = Eff CompileOp`**. The generated monadic fold is for `Except`, `Option`, `StateT`, `IO`. It is
not the tool for producing a plan.

So the factoring is forced and is also the better one: a pure fold `Eff Op → Eff CompileOp` (or
`Representation → Eff CompileOp`) produces a **plan as data**, typed by `TypedProgram`, run by the
machine, replayable from a tape, meaningful on the straight fragment by `denote`
(`Laws/Program/Denote.lean:66`). Building the plan is a `cata` into the carrier `Eff CompileOp`
with `Eff.bind` as sequencing, a perfectly good algebra that simply is not a monad. The design
should not claim a Kleisli lift it cannot have in Lean.

Two cautions about `foldM` even where it applies. `foldM_eq_cata_eff`
(`Program/Fold.lean:2521`) says `foldM_eff alg node = cata_eff alg.toSeq node`: the monadic fold is
definitionally a `cata` into `M (R .fam)` with the `do`-binding baked in **at generation time**, so
the effect order is the declaration order of the recursive arguments and no algebra can change it.
And the algebra's operations receive already-run values (`:2344`: `let x0 ← foldM_eff alg a0` then
`alg.eff_bind x0 x1`), so an algebra cannot decline to run a child; with `Except` that is
harmless, with a real effect every subtree's effects fire before the parent decides anything. If a
compile needs short-circuiting or a different order, `foldM` as generated does not suffice and the
algebra must take `M`-valued arguments, which is a different generator. Decide before S9.

**(b) What `CompileOp` must contain.** Five rows: `readTable (key) : Document` (one row, not four:
the template table, syntax table, code table and row table are all P2 documents in the store);
`moduleSurface (query) : Document` (S8); `checkHost (source, config) : Diagnostics`, with
`HostConfig` in the **request** so it lands in the digest; `emit (path, bytes) : Unit`, the only
write; `resolve (digest) : Document` if the plan is content-addressed. Two that look tempting and
are not rows: `parse` (it is at the boundary and its result is a document, so it returns through
`readTable`), and anything answering with a Lean function.

*The unpriced cost.* Every row needs request and answer types in the row table, and the `Eff` type
language is `Ty` (`Program/Fold.lean:34`), in which `Document`, `Diagnostics` and `HostConfig` are
not expressible. Either keep documents behind an opaque handle (`Ty.handle` exists,
`Program/Fold.lean:42`, and handles are the estate's existing move for store values) or widen
`Ty`. I would take handles. Without this ruling S9 cannot start, and the design does not mention
it.

**(c) The theorem.** Naturality. Let `σ : Eff Op → Eff CompileOp` be the plan fold,
`π : Eff Op → Except PrintRefusal Tree` the pure template fold, `H` a handler answering every
`CompileOp` row from the tables as data. Then `denote (σ e) under H = π e` on the straight
fragment: the plan's meaning agrees with the pure fold whenever the effects answer as the tables
say. That is two folds into different carriers with a map between them, which is a fusion
statement and needs `AlgMap` for `Eff`. **This is the second independent place in this note where
the missing `cata_X_fusion` is the right tool**, which is reason enough to add it now.

`foldM_natural_eff` (`Program/Fold.lean:2731`) is **not** this theorem and should not be cited as
it: it moves one `foldM` along a `MonadMorphism` (`:19`) between two Lean monads, and neither side
here is a Lean monad in the required sense.

---

## Q10. Retiring `Effects`, and how far to formalize

**(a) What the repository still takes.** Enumerated, not sampled. Exactly four modules under
`src/` import the package. `Laws/Program/Denote.lean:3` imports `Effects.Algebra.Laws` and uses
`Effects.Signature` for `StoreSig` (`:41`), `Effects.Program` as the meaning's carrier (`denote`,
`:66`), `interpret`, `interpret_bind`, `interpret_perform`, `Program.bind_assoc`.
`Laws/Program/Sched.lean:2` imports `Effects.Algebra.Sum` and uses `Signature.sum` for `RSig`
(`:196`), `Program.inl`, `interpret_inl`. `Machine/Context.lean:4` imports
`Effects.Algebra.Program` and uses `Effects.Signature` for the service-access signature (`:102`),
`Effects.Program` (`:108`), `Program.pure`/`vis` for a `UsesOnly` predicate.
`Schema/EffectfulField.lean:2` imports `Effects.Algebra.Laws` **and** `Effects.Flow.Block` and
opens the namespace (`:16`).

The consumed surface by name: `Signature`, `Signature.sum`, `Program` with
`pure`/`vis`/`bind`/`perform`/`inl`, `Handler`, `Handler.sum`, `interpret`, and about eight laws.
Roughly 250 lines of `Effects/Algebra/`, plus `Effects/Flow/Block.lean` (273 lines) for one schema
module.

**This is already ruled.** DI-90 (`docs/DESIGN-ISSUES.md:164`): bring the consumed algebra core
in-tree under the same names, drop the pin, in M3 with the proofs, no rewrite of the free monad,
proof chain unchanged. So the owner's ask restates a standing ruling; what this scout adds is the
size above and one gap: **`Effects.Flow.Block` is not part of the consumed algebra core** and is
used by exactly one module. Whether the flow block terms come in-tree too, or that module drops
the dependency, is a separate decision DI-90 does not cover.

**(b) Can the layout core and the template layer stand without it? Yes, trivially.**
`lean4-doc/lakefile.toml` declares no dependencies at all, and the `Tm` of Q8 needs only
`DecidableEq`. Nothing in P4 or P5 touches a free monad with functional continuations, and as the
precedents note argues (§14.7) neither may, because both carriers need decidable equality and
canonical bytes. Retiring `Effects` is **orthogonal** to this line of work and should not be used
as a reason to keep it. The risk is the opposite: coupling S1 to M3 for no reason.

**(c) "Not being afraid to really formalize this."** Worth **proving**, because the proof changes
what can go wrong: initiality per signature (`hom_eq_cata_*`; present for `Eff` and `Doc`, wanted
for `Tm` and `Expr`); fusion (`AlgMap` plus `cata_X_fusion`), generated, the tool for three
obligations in this note and present in exactly one place today (`Doc/Core.lean:120`); the
template layer as a section and a retraction on a characterised image (Q4(c)), which is the round
trip the estate pays 3531 lines for; well-bracketing and containment of the annotation stream, on
which `locate` and every diagnostic mapping rest; the measure as a monoid homomorphism out of the
stream and the house layout as one out of the document.

Worth **stating and not proving**, because the proof would be a restatement: "templates are a
natural transformation into the free monad over the syntax signature" (naturality in the carrier
is parametricity, not available as a Lean proof without extra machinery; state the shape, prove
the two concrete equations); "the compile is a Kleisli lift of a fold" (true as description,
unavailable while `Eff` is not a `Monad`; prove the concrete naturality equation); "layout is a
fold into a measured monoid with a policy as a choice function" (the content is laws 1 to 6).
Coherence of projections over paths sits between: write a small record with three fields (the
fold, the path yield, the commutation with `Node.child`) and prove the three instances (`spans`,
the containment tree, `blame`); do not attempt a theorem quantified over all projections.

Not worth stating at all: presheaves, second-order signatures, free Σ-monoids. Naming the
categorical ancestor in a docstring is useful; carrying it in the types is what the estate already
rejected, and the first-order `Slot` encoding is sound and guarded (`Forms.lean:198`).

**On the owner's "built in tree type" question**, checked rather than recalled.
`…/lean4---v4.33.1/src/lean/Init/Data/Format/Basic.lean`: `Format` (`:55`) has `nil`, `line`,
`align (force)`, `text`, `nest (indent : Int)`, `append`, `group (behavior : FlattenBehavior)`,
`tag : Nat → Format → Format` (`:102`), and derives `Inhabited` only. So annotations are `Nat`,
not a type parameter, and `Doc Path` would need a side table; `nest` takes an `Int`; a `text` node
may contain newlines by documented design (`:82`); `group` is unary with two flatten behaviours
(`allOrNone` and `fill`, `:34`) and `fill` is not a binary choice; there is no hard-break
constructor; there is **no `DecidableEq`, no `BEq`, no `Repr`**; and both `be` (`:252`) and
`spaceUptoLine'` (`:209`) are `partial`, so the renderer has no kernel equations and nothing about
it can be proved. `MonadPrettyFormat` (`:220`) with `pushOutput`, `pushNewline`, `startTag`,
`endTags` is a good template for the stream shape and is the one thing worth copying. **The answer
is no**, and `partial` alone settles it.

---

## Ranked changes to the first pass, before it grows

1. **Make `text` newline-free by construction.** A smart constructor splitting on `'\n'` into
   `text`/`hardline` with the raw constructor private, or a decidable `WellFormed` with a guard.
   Everything downstream of `Measure.ofText` (`Doc/Measure.lean:59`) is wrong on a newline-bearing
   string, including the bridge from `lines_house` to `containsNewline`. One hour, removes a class.
2. **Prove the containment half of law 5 and restate `locate` on it.** Without
   `spans_disjoint_or_nested` and `locate_innermost`, `locate` (`Doc/Layout.lean:150`) is a
   heuristic and S3 has no foundation.
3. **Parameterise `locate` by the offset unit.** It hard-codes `sp.start.bytes` (`:151`) while
   `tsgo` reports UTF-16. `Span` already carries the whole `Measure`; take a projection.
4. **Fix law 6's wording and add the determinism corollary.** The house layout is a function of
   the document *and the indentation*; `render` is a function of the document.
5. **Add `AlgMap` and `cata_X_fusion` to `tools/Effect4Gen/Fold.lean` and regenerate.** The tool
   for the `Eff` analogue of `layout_info`, for Q9's naturality theorem, and for
   `weaken_eq_cata_eff`'s hand proof; it also makes `Doc/Core.lean` a mirror rather than a
   parallel mechanism.
6. **Add a maximum-width field to `Measure`, or delete `columns`.** `Measure.append` sums
   `columns` (`Doc/Measure.lean:33`), making it a character count and not a width, and no field is
   the maximum line width, so Bernardy's measure cannot be formed and the specification's badness
   cannot be computed. Adding a field later moves every proof.
7. **Rename `elastic` or state its limit in the module.** It is a local `fits` with no lookahead
   (`Doc/Layout.lean:99`) and cannot become Bernardy without changing `Policy` (`:37`).
8. **Make `group` the only public way to build a choice**, or add `isFlat` as the precondition
   under which `infoAlg.choice`'s `width` is exact (`Doc/Core.lean:170`).
9. **Generate an `Expr`/`Stmt` algebra for `lean4-typescript`.** S2's fusion lemma has no tool
   otherwise, and the package has no `cata` today.
10. **Write the `stmts` encoding into the S2 packet** before anyone starts: indent before each
    statement, newline after each including the last (`Render.lean:275`).
11. **Split design §9 laws 4 and 9.** Law 4 is a stream law with a house corollary; law 9 is a
    `Prop` in general and a `decide` at the native table.

---

## Risks for the whole line

- **The image predicate is load-bearing and is not in the plan.** Laws 12 and 14 both rest on
  `InImage`, which the design mentions only as the phrase "on the image". If S4 lands the table
  without it, S5 will find the tie-break unjustified and the strong half of the round trip
  (`read_exact`, today with no `readable` premise) will get weakened to ship. A regression dressed
  as progress.
- **Two template calculi will be conflated.** `Forms.Template` is over `Eff`; the new table is
  over `Tree`. Design §3 says they merge. They do not.
- **Renderer injectivity is unpriced.** The only genuinely new proof with no analogue in the
  estate, and what makes `Fmt` worth stating. If it proves expensive the fallback is the executed
  host check; say so now rather than in S5.
- **`Policy` cannot grow into the layout specification's engine.** The specification promises an
  optimal, badness-bounded layout; this `Policy` can express only greedy choices. Either the
  promise is withdrawn or the carrier changes.
- **A fourth Lean package has a fixed cost.** `lean4-doc` pins `leanprover/lean4:v4.33.1`, which
  matches. The precedents note's mitigation (put `Doc` inside `lean4-typescript`) is worse for the
  containment tree, which has nothing to do with TypeScript. I would keep the separate package and
  accept the cost, but it is decision 1 of design §11 and it is the owner's.
- **`Ty` cannot express a `Document`.** Q9's `CompileOp` rows need types the checker can type.
  Without a ruling on handles versus widening `Ty`, S9 cannot start.
- **Coupling the `Effects` retirement to this line.** DI-90 puts the algebra core in-tree in M3.
  Nothing in P4 or P5 needs it. Sequencing them together makes S1 wait on M3 for no reason.
- **Design §12's MCP and CLI face** rests on the same `Ty` gap as Q9(b) and on the schema
  combinator printer that does not exist (Q6). Both are upstream of S9 and neither is a stage.
