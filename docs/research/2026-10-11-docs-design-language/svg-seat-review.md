# Review of seat SVG, slices S0 to S2 (2026-10-11)

The lean4-effect4 coordinator wrote this review at the owner's request. It reads branch `html/svg`
at `9266dac`, and the S2 files not yet committed: the reader, the shared emitter, the generated
schema and its battery. The owner wants this package held to
the standard of lean4-effect4. Its design rests on a theory we can reason with, not on its
literal cases.

**First, before you continue.** S0 and S1 stand as landed, and S2 continues. Before S3, rewrite
sections 4, 5.2, 5.3 and 6 of `docs/SVG-PACKAGE-PLAN.md` on the model of section 2 below:

- one top-down tree automaton;
- one walk with several algebras;
- every finite set as a bitset;
- the value grammars as one invertible regular grammar.

Start a research partner on the theory packet now (section 7). It runs beside S2.

## 1. What landed

| Commit | Slice | Verdict |
| --- | --- | --- |
| `0fe19fd`, `ef73684` | the claim; ruling R-S1 | Good. R-S1 records the owner's direction. |
| `e74dc0d` | S0, the merge | Good. R-S2 records the four answers to the trust gate, the measured counts and debts D75 to D77. |
| `9266dac` | S1, the plan and the pin | Good. The pin is sealed and cross-checked. The plan places its claims and lists its limits. |
| not committed | S2, the reader, the emitter, the schema | Good. Commit it after the five reader repairs of section 5. |

S2 already does four things this review asks for:

- `WhatwgGates/EmitLean.lean` is one emitter for both schemas, moved out of the HTML emitter
  with its bytes kept. This is the deep-module move.
- The readings hold `a`'s transparency as data: `inherits`, `through` and `excluded`.
- Every generated file carries the licence notice.
- Each line of `WhatwgTest/Svg/Schema.lean` is a finite evaluation or a control.

These parts of the plan stay:

- the authority order;
- a dangling name as a row, with a fixed meaning;
- readings pinned by digest;
- `RawNode` unchanged, with the namespace inherited down a path;
- a located refusal, complete against `validIn`;
- a retraction claimed only modulo a named normaliser;
- the list of what the graph does not establish (plan, section 6).

**What is missing is the model under the plan.** The plan names hand-written functions:
`validSvg`, `SvgCtx.integration`, `renderIn`, and a reader and a printer per grammar. It then
proves each law about a pair of them. Such a law is a pairwise fact, and each new function needs
its own proof again. Instead, state the structure once. Each law is then an instance of it.
lean4-effect4 works this way: two folds agree when their algebras do (`hom_eq_cata_eff`).

## 2. The model

### T1. Validation is a top-down deterministic tree automaton

A `RawNode` is an unranked ordered tree, a hedge. A checker of content models with transparency
and exclusions is a top-down deterministic hedge automaton:

- a state is a context: what may stand at a position;
- the transition takes a state and an element's name to the context of its children;
- acceptance at a node is a local test of the state, the node's name, its attributes and the
  names of its children.

In the taxonomy of Murata, Lee, Mani and Kawaguchi this is a single-type tree grammar. The type
of a child is a function of its parent's type and its own label, and `Ctx.child` is that
function. Three facts follow:

1. Validation is one top-down pass. It never backtracks.
2. The reachable states are finite. A test can enumerate them, and `decide` can check a property
   at every reachable context.
3. The class is closed under product. The HTML automaton and the SVG automaton compose into one
   automaton, whose state is the sum of their states.

### T2. The namespace is a component of the state

The state of the composed automaton is a sum:

```lean
inductive Pos where
  | html (c : Whatwg.Html.Content.Ctx)
  | svg (c : Whatwg.Svg.Content.Ctx)
```

The tree construction of the HTML Standard has its own small automaton on namespaces. It enters
SVG at `svg`, and it returns to HTML under `foreignObject`, `desc` and `title`. Write it once, in
the seam, with its source anchor:

```lean
inductive Ns where | html | svg
def Ns.step : Ns → List Char → Ns
```

The law that ties the checker to the parser is a homomorphism of automata:

```lean
theorem Pos.child_ns (p : Pos) (name : List Char) : (p.child name).ns = p.ns.step name
```

The printer's state is `Ns` with the raw-text bit, never `Pos`. Both the checker and the printer
factor through `Ns.step`, so they cannot disagree about a node's namespace. N3 says that no SVG
element name ends foreign content. It is what makes `Ns.step` the parser's own function on a
valid tree.

### T3. A content model is an element of a finite Boolean algebra

An SVG content model is a set of admitted child tags with a text bit: an element of
`Set Tag × Bool`. The kinds of the definitions spell points of that algebra:

- `anyof` is the union of the listed elements and of each listed category's members;
- `any` is the top element;
- `text` is the text bit alone;
- `textoranyof` is `anyof` with the text bit.

Category resolution is the unique join-homomorphism from the free join-semilattice on names. It
sends an element name to its singleton, a category to its members, and a dangling name to the
bottom element (SV-3). The generator computes it, and the library holds its value.

**The SVG `a` element is transparent.** Its sealed definition reads: "any element or text
allowed by its parent's content model, except for another a element". Under a `switch`, the
model in force is the model of the nearest ancestor that is not a `switch`. So the SVG grammar is
not local either, and `SvgCtx { model : Tag, inAnchor : Bool }` is the wrong state. The state has
the HTML context's shape:

- the model in force;
- the model of the nearest ancestor that is not a `switch`;
- the exclusions.

**Two readings count.** `feDiffuseLighting` and `feSpecularLighting` take exactly one light
source, and `animateMotion` takes at most one `mpath`, in any order. So an SVG content model is
unordered, with a count interval per group of labels. This is a disjunctive multiplicity schema
(Boneva, Ciucanu and Staworko). Its membership test reads only the multiset of the children's
labels: every label is admitted, and each group's count is in its interval. The model is then:

- a set of admitted labels and a text bit;
- a list of intervals, each over a set of labels;
- for a transparent element, the inherited model, the `switch` skip and the exclusions.

Transparency passes the model through. An exclusion is an SGML exception (Kilpeläinen and Wood):
a set that only grows along a path. Two laws hold for every such context. Prove each once, over
both namespaces:

- the exclusions only grow: `c.excl ≤ (c.child t).excl`;
- the admission of a tag is antitone in the exclusions.

The HTML package proves both today, for HTML alone (`child_excl_le`, `admits_antitone`).

### T4. A finite set over a generated universe is a bitset

Every finite set of the schema is a subset of a generated enumeration: tags, attributes,
categories, exclusion flags. Represent each as a `Nat` mask over the constructor index:

- membership is `mask.testBit t.index`;
- union is `|||`, intersection is `&&&`, and inclusion is `a ||| b = b`;
- the laws of a Boolean algebra are core lemmas (`Nat.testBit_or`, `Nat.testBit_and`).

The kernel evaluates `Nat` arithmetic and its bit operations natively, by GMP. So one definition
is both the specification and the fast test. No pair like `excludedSpec` and `excluded` is
needed, and a tactic reads a mask back as one literal. The research partner confirms the kernel's
list at the toolchain `v4.33.1` (section 7).

### T5. One walk, several algebras

`validIn`, the located refusal and the printer are three folds over `RawNode` with one inherited
attribute. An attribute grammar with inherited attributes is a catamorphism into functions of
those attributes (Fokkinga, Jeuring, Meertens and Meijer). So write the walk once. The algebra
also sees the raw children, because `seqOk` reads their names, so the walk is a paramorphism:

```lean
/-- A top-down walk: a state, its transition, and what each node makes of its children. -/
structure Walk (S R : Type) where
  step : S → List Char → S
  element : S → List Char → List (List Char × List Char) → List RawNode → List R → R
  leaf : S → RawNode → R

mutual
def Walk.run (w : Walk S R) (s : S) : RawNode → R
  | .element name attrs children =>
    w.element s name attrs children (w.runAll (w.step s name) children)
  | node => w.leaf s node
def Walk.runAll (w : Walk S R) (s : S) : List RawNode → List R
  | [] => []
  | n :: ns => w.run s n :: w.runAll s ns
end
```

This is a sketch: the spellings follow `RawNode` as it stands. Two laws, each proved once by
induction on `RawNode`:

- **W1, fusion.** If `h` commutes with the node maps of `A` and `B`, then
  `h (A.run s n) = B.run s n`.
- **W2, state homomorphism.** If `f : S → S'` commutes with the transitions and the node maps
  factor through `f`, then `A.run s n = B.run (f s) n`.

Then:

- `explain_none_iff` is W1 at `Option.isNone`, from the refusal algebra to the Boolean one. It
  needs no second induction.
- The printer's agreement with the HTML printer on a tree without SVG (P1), and the namespace
  agreement of T2, are W2 at `Pos.ns`.
- `validIn` stays the kernel's function if it measures faster. A connector
  `validIn c n = boolWalk.run (.html c) n` is then proved once, and the laws move to the walk.
  This is the rule "build in parallel, slot in, delete": the walk lands beside `validIn`, and
  the callers move after.

### T6. A name table is an exact embedding

A name table is a write–read pair, `name : Tag → List Char` and
`ofChars? : List Char → Option Tag`, with three laws:

- it is total on its domain;
- the retraction: `ofChars? (name t) = some t`;
- the exactness: `ofChars? s = some t → s = name t`.

Plan node N1 proves the first two "by one decide per constructor". Prove each law once per
table instead:

- the retraction by one `decide` over the census, as the S2 battery evaluates it;
- the exactness by one `split` over the generated `ofChars?` match, whose every arm closes by
  `rfl`.

If a third table needs the same proof, build the lookup generically from the list of pairs.
Then prove the two laws once for all tables.

Case restoration (N2) is an exact embedding modulo a normaliser: `restore (lower n) = n` for every
schema name, where `lower` is the parser's normaliser.

### T7. The printer is an exact embedding on well-formed trees

The HTML package already proves more than P1: `decode_render` and `render_injective_of_wf`. Keep
that strength in S3:

- index `wf` and the decoder by the print state of T2;
- in SVG no element is void and no text is raw;
- prove `decode_render` for trees that hold SVG.

Then the consumer has an exact embedding of valid well-formed trees into characters, not only a
connector on trees without SVG.

### T8. Every value grammar of S4 is regular

Path data, `points`, `viewBox`, the number, the length and the SVG `transform` list are regular
languages: no production nests. So S4 is one library, not five reader–printer pairs:

- **The grammar is data.** It is a regular expression over character classes. The gate compares
  it with the BNF of the sealed chapter, as the HTML gate compares its element rows.
- **The typed value goes through one invertible description** of the grammar, which both reads
  and prints. Its erasure is that expression (Rendel and Ostermann; Kennedy's pickler combinators).
- **Three laws are proved once, over the description:**
  - V1, the retraction `read (print v) = some v`, with V2 as its corollary;
  - V3a, the soundness of `read` against the expression's language: an accepted string is in
    the language, through a derivative matcher (Brzozowski; Owens, Reppy and Turon);
  - V3b, the completeness of `read` against that language, which needs the grammar's
    longest-match rule. It stays open per grammar, with the specification's own examples as
    finite evidence. Verbatim's longest-match lexer is the model to read.

Each grammar then costs its transcription and nothing more. V3 stops being "open, not planned":
the soundness of `read` is proved.

**The number** is a decimal: an element of the ring `ℤ[1/10]`. Its record is a normal form, an
integer mantissa and a power of ten with no trailing zero in the mantissa. Write the invariant
as a predicate, and normalise in one function. A conversion from a rational with rounding is a
widening, not an embedding. The consumer's layout numbers cross it, so state its bound.

### T9. The schema projection is a function of sealed bytes

S2 is a function from the sealed XML to the projections and the schema modules. The drift gate
is its evidence (G1). Two points of the reading:

- A list attribute holds names with spaces (`graphics referencing`, `document element event`).
  Split it on commas and trim. Never split it on white space.
- XML normalises an attribute value: each white-space character becomes a space (XML 1.0,
  section 3.3.3). Apply that in the reader, or state that the reader keeps raw values and the
  projection normalises them.

## 3. Changes to the plan

| Plan section | Change |
| --- | --- |
| 4, SV-7 | Read `svg` from the HTML Standard's own category lists. The sealed `source` lists `SVG svg` and `MathML math` under flow, phrasing, embedded and palpable content. The HTML gate reads those items, and the HTML `Tag` gains two foreign tags. Admission is then the existing `admitsWith`, exclusions included. Drop `Base.holdsPhrasing`. |
| 4, SV-8 | Recommend `desc` as phrasing content, like `title`. The HTML Standard narrows `title` and `foreignObject` and says nothing of `desc`. The smaller admission can widen later without breaking a tree; the larger cannot narrow. The owner rules. |
| 4, SV-4 | `a` is a reading of transparency with `switch` skipped (T3), not a fixed set. |
| 4, SV-20 | Recommend the strict ceiling from the first module. |
| 4, new | SV-22: every finite set of the schema is a bitset over its universe (T4). SV-23: the checker, the refusal and the printer are one walk (T5). SV-24: a name table is an exact embedding built generically (T6). SV-25: a value grammar is a regular expression as data, read and printed through one invertible description (T8). |
| 5.2 | Replace `SvgCtx` by the context of T3. Replace `validSvg` and `validSvgAll` by the walk. Replace `Mode` by `Ns` from the seam. |
| 5.3 | One library module, `Whatwg/Svg/Value/Grammar.lean`, holds the description and its laws. Each grammar is one small module. |
| 5.3, `transform` | The consumer writes `transform="scale(…)"` and `xml:space="preserve"` today (`tools/Tools/View/Output.lean`). So S4 needs `transform`. Recommend pinning the SVG transform grammar of CSS Transforms 1 at one commit, and the CSS number only as far as SVG's own `number` production. |
| 6 | C3 and P1 become instances of W1 and W2; add W1 and W2 as nodes. N1 gains its exactness from the generic lookup. V3 splits into V3a (proved, generic) and V3b (open, per grammar). Add P3, injectivity on trees with SVG (T7). |
| 6, every node | Name its consumer: lean4-effect4's document builder (`tools/Tools/Document/Html.lean`) or its picture writer (`tools/Tools/View/Output.lean`). |

## 4. The meta level: tactics, elaboration of `html!`, macros and generated code

**M1. The de Bruijn criterion.** Meta code builds terms and writes messages. It decides nothing
that the kernel does not decide again. Every judgment lives at object level: `validIn`,
`explain`, the grammar laws.

**M2. One refusal.** Today three functions describe a failure in prose:

- the `admits` tactic;
- `attrProblem?` and `valueProblem?` in `Whatwg/Html/Content/Valid.lean`;
- lean4-effect4's own walk, `problem?`, in `tools/Tools/Document/Html.lean`.

After S3 there is one. The tactic and the consumer render the refusal of `explain`. The tactic's
message is then complete by `explain_none_iff`.

**M3. Reification.** `Whatwg.Html.Admit.excl?` reads the fifteen fields of `Exclusions` back
from an `Expr` by hand. Under T4 a mask is one `Nat` literal. Write no second hand reader for the
SVG context.

**M4. The kernel's cost model.** These rules hold for code the kernel evaluates, which is
everything under `html!` and `decide +kernel`:

- Recurse structurally. The kernel does not unfold a well-founded definition.
- Compute with `Nat` and `Bool`. The kernel evaluates `Nat` operations natively.
- Avoid `String` operations. The package already spells names over `String.toList`.
- Measure each change with `WhatwgTest/Html/DecideBenchmark.lean`, before and after.

**M5. `html!` for SVG.** SVG names are case-sensitive, and some hold `:` (`viewBox`, `xml:space`,
`xlink:href`). The syntax keeps each spelling exactly: a string literal for a name that is not an
identifier. It declares no token that the trust gate refuses (R-S2 found `</`). Lean's macro
hygiene (Ullrich and de Moura) keeps the macro's names from capturing a user's.

**M6. Generated code is data.** The generator emits enumerations, tables, masks and pinned
readings. A generated `match` that holds one row per tag is a table, and it is fine. A function
with logic over the tables is written once, by hand and generically. A generated function with
logic, or a generated theorem per constructor, is a defect.

**M7. Reflection once per class.** `Tag.mem_all`, `Base.mem_all`, `forall_tag_of_all` and
`forall_base_of_all` state one fact once per universe. Give the package one class for a finite
universe. It holds the list, the proof that the list holds every value, and no duplicates. Prove the reflection lemma once. The SVG
generator emits instances of the class.

**M8. Proof style.** lean4-effect4 holds every new and touched proof to these rules:

- A `simp` names its lemmas: `simp only [...]`.
- No `simp_all`, `first | …` or `try`: a fallback that fails silently hides a missing lemma.
- A proof takes its case list from the definition (`fun_induction`, `fun_cases`), not from
  `cases a <;> cases b`.
- One lemma per predicate, with a catch-all alternative where it holds, not one lemma per case.
- Under a strict prefix, check what each tactic reaches. `grind`, `by_cases` on a proposition
  with no decision, and `simp` deciding `String` equality each reach `Classical.choice`.

## 5. The reader of S2, `WhatwgGates/Xml.lean`

1. Use core `List.span` in place of `spanWhile`.
2. Refuse a non-ASCII character in `read`, with its offset. A span is then a byte span by
   construction, and no caller checks.
3. Read a name fail-closed. Its first character is a letter, `_` or `:`, the ASCII part of
   XML's `NameStartChar`.
4. `Node.span` returns `(0, 0)` for text, a junk value. Return an `Option`, or keep a span only
   where one exists.
5. Normalise attribute values, or say that the reader does not (T9).

The fuel is fine for a gate. Fuel is the input length plus one, so the branches that report
"ran out of fuel" are dead. Say so in the docstring.

## 6. The HTML package, to the same standard

None of these blocks S2 to S4. Record each as a debt, with the slice that pays it:

- **H-C1.** Exclusions as a bitset. Today they are fifteen `Bool` fields, the list of rules is
  written four times (`hits`, `excluded`, `hitsWith`, `excludedWith`), and two
  specification–fast pairs repeat it.
- **H-C2.** One class for a finite universe and one reflection lemma (M7).
- **H-C3.** Proof style (M8). Unnamed `simp` calls: 49 in `Print/Render.lean`, 11 in
  `Content/Valid.lean`, 7 in `Content/Context.lean`. `simp_all` in `Content/Context.lean`.
- **H-C4.** The tactic's hand reader (M3) and its prose (M2).
- **H-C5.** Duplicate character helpers: `spanChars`, `spanWhile`, two `isNameChar`, `nameChar`.
- **H-C6.** `validIn` as the Boolean algebra of the walk (T5), after a measurement.

## 7. The research partner

Start a research partner now, as a subagent of your session. Its prompt is
`docs/research/2026-10-11-svg-theory-prompt.md`. It builds the theory packet
`docs/research/2026-10-11-svg-theory/` while you continue S2. Read the packet's README before
the plan revision. The packet's full texts stay on disk and out of git: add
`docs/research/2026-10-11-svg-theory/texts/` to `.gitignore` before the partner starts. Its
README, its citations and its short excerpts are committed.

## 8. Order

1. S2 as designed, with the reader repairs of section 5. Commit it and hand back.
2. The plan revision of section 3, as one commit. The owner rules on SV-8, SV-20 and the CSS pin
   at that handoff.
3. S3 in five parts:
   - S3a, the context of T3 and the bitsets of T4, for SVG;
   - S3b, the walk, its two laws, and the connector to `validIn`;
   - S3c, the refusal algebra, and `explain_none_iff` by W1;
   - S3d, the print state, the decoder, and injectivity with SVG;
   - S3e, the tactic and `html!`.
4. S4 in three parts:
   - S4a, the grammar library and its generic laws;
   - S4b, the number, path data, `points` and `viewBox`;
   - S4c, `transform`, after the CSS pin.

Each part lands with its narrow build, its axiom receipt and the gates it reaches (`AGENTS.md`,
"Gates").
