import Effect4.Laws.Api.Codegen
import Effect4.Laws.Program.CheckedTyping
import Effect4.Laws.Program.ReferenceTyping

/-!
# Test.Program.ReferenceExpansion — the reference expansion on real programs: finite controls

`expanded_refs_nil_of_wf` (`src/Effect4/Laws/Program/ReferenceExpansion.lean`) is the law: a
program whose layer references are well formed expands to a program with no reference site, at
the bound of `Eff.expandRefs`. This battery evaluates the premise and the conclusion on nine
programs over the native alphabet. They are the finite cases of Codex's model
(`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/roadmap-audit/proofs/probe.py`),
written as real programs.

- Five programs have well-formed references: no reference, one reference, a chain of nested
  references, a diamond, and targets nested in a target. Each expands to a program with no
  reference site. The count of the sites is pinned round by round, and the diamond's count grows
  before it falls.
- Four programs are the red controls, one for each way that `Eff.layerRefsWF` refuses: a
  reference inside its own target, a forward reference, a target that is a reference, and a
  missing target. Each fails `Eff.layerRefsWF`, at its own clause.
- The two consumers are applied without the premise that they carried
  (`typeOfProgram_expandRefs`, `checkTypedProgram_of_hasTy`), and the checker's equation is
  evaluated (`typeOfProgram_eq_if_refsWF`). One red control drops the premise that
  `typeOfProgram_expandRefs` keeps.
- The checker tests the references' formation only (decisions row 273, point 2), and the
  facade's refusal (`Api.explain`, `src/Effect4/Api.lean`) has no arm for a reference site that
  the expansion keeps. The nine programs keep each answer: the checker's, and the facade's
  refusal. A tenth program has well-formed references and a body that the checker refuses. No
  program is at the arm that the facade lost (proved).

Placement. Each guard is a finite instance of the registry claim
`reference-expansion-complete` (concept `initial-algebras-folds`, requirement R5). A program
outside the ten is not checked here: the theorem is the general statement. The battery states
nothing about a run.
-/

set_option autoImplicit false

namespace Test.Program.ReferenceExpansion

open Effect4 Effect4.Program Effect4.Machine

/-! ## The programs -/

def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩

/-- A layer with no reference. -/
def leaf : LayerTerm NativeOp := .succeed key (.nat 7)

/-- A program around one layer: the layer is at the path `[0]`. -/
def around (l : LayerTerm NativeOp) : NativeEff := .provideLayer l false (.service key)

/-- No reference. -/
def noRef : NativeEff := around (.merge leaf leaf)

/-- One reference, at `[0, 1]`, to the layer at `[0, 0]`. -/
def oneRef : NativeEff := around (.merge leaf (.ref [0, 0]))

/-- A chain: the reference at `[0, 1, 1, 1]` names a layer that holds a reference to a layer
that holds a reference. -/
def chain : NativeEff :=
  around (.merge leaf
    (.merge (.fresh (.ref [0, 0]))
      (.merge (.fresh (.ref [0, 1, 0])) (.ref [0, 1, 1, 0]))))

/-- A diamond: three references to a layer that holds three references to one layer. -/
def diamond : NativeEff :=
  around (.merge leaf (.merge
    (.merge (.ref [0, 0]) (.merge (.ref [0, 0]) (.ref [0, 0])))
    (.merge (.ref [0, 1, 0]) (.merge (.ref [0, 1, 0]) (.ref [0, 1, 0])))))

/-- Targets nested in a target: the layer at `[0, 0]` is a target, and it holds two targets and
the references to them. -/
def nestedTargets : NativeEff :=
  around (.merge
    (.merge leaf (.merge (.fresh (.ref [0, 0, 0])) (.ref [0, 0, 1, 0])))
    (.ref [0, 0]))

/-- Red: a reference inside its own target. -/
def insideTarget : NativeEff := around (.fresh (.ref [0]))

/-- Red: a forward reference. -/
def forward : NativeEff := around (.merge (.ref [0, 1]) leaf)

/-- Red: a target that is a reference. -/
def refTarget : NativeEff := around (.merge leaf (.merge (.ref [0, 0]) (.ref [0, 1, 0])))

/-- Red: a target that names no layer. -/
def missing : NativeEff := around (.merge leaf (.ref [0, 0, 5]))

/-- The tenth program: `oneRef`'s layer, with well-formed references, and a body that the checker
refuses, `fail` at a Boolean. The body is at the path `[1]`, past the reference site `[0, 1]`. -/
def refusedBody : NativeEff :=
  .provideLayer (.merge leaf (.ref [0, 0])) false (.fail (.lit (.bool true)))

/-! ## The instruments -/

/-- The program after `k` rounds: the fold of `Eff.expandRefs`, at any count of rounds. -/
def rounds (root : NativeEff) (k : Nat) : NativeEff :=
  (List.range k).foldl (fun acc _ => Eff.expandRound (.eff root) acc) root

/-- `Eff.expandRefs` is the rounds at one more than the count of the reference sites. -/
theorem rounds_expandRefs (root : NativeEff) :
    rounds root ((root.refSites []).length + 1) = root.expandRefs := rfl

/-- The count of the reference sites after 0, 1, …, `n + 1` rounds, where `n` is the count of the
program's own sites. The last entry is the count in `Eff.expandRefs`. -/
def counts (root : NativeEff) : List Nat :=
  (List.range ((root.refSites []).length + 2)).map fun k => ((rounds root k).refSites []).length

/-- The three clauses of `Eff.layerRefsWF` at each reference site, in program order: the target
precedes the site, the target does not enclose the site, and the target names a layer that is no
reference. The third clause reads the layer through `LayerTerm.refSite`, which yields a site
exactly at a reference, so this battery adds no case on the program family. -/
def clauses (root : NativeEff) : List (Bool × Bool × Bool) :=
  (root.refSites []).map fun x =>
    (Path.lt x.2 x.1, !Path.properPrefix x.2 x.1,
      ((Node.eff root).layerAt x.2).any fun l => (LayerTerm.refSite l []).isEmpty)

/-- The nine programs. -/
def programs : List NativeEff :=
  [noRef, oneRef, chain, diamond, nestedTargets, insideTarget, forward, refTarget, missing]

-- The clauses are the definition's: on each program their conjunction is `Eff.layerRefsWF`.
#guard programs.all fun p => p.layerRefsWF == (clauses p).all fun c => c.1 && c.2.1 && c.2.2

/-! ## Green: well-formed references, and no reference site after the rounds -/

#guard noRef.layerRefsWF && oneRef.layerRefsWF && chain.layerRefsWF && diamond.layerRefsWF &&
  nestedTargets.layerRefsWF

-- The sites of each program, as `(site, target)` in program order.
#guard noRef.refSites [] = []
#guard oneRef.refSites [] = [([0, 1], [0, 0])]
#guard chain.refSites [] =
  [([0, 1, 0, 0], [0, 0]), ([0, 1, 1, 0, 0], [0, 1, 0]), ([0, 1, 1, 1], [0, 1, 1, 0])]
#guard diamond.refSites [] =
  [([0, 1, 0, 0], [0, 0]), ([0, 1, 0, 1, 0], [0, 0]), ([0, 1, 0, 1, 1], [0, 0]),
   ([0, 1, 1, 0], [0, 1, 0]), ([0, 1, 1, 1, 0], [0, 1, 0]), ([0, 1, 1, 1, 1], [0, 1, 0])]
#guard nestedTargets.refSites [] =
  [([0, 0, 1, 0, 0], [0, 0, 0]), ([0, 0, 1, 1], [0, 0, 1, 0]), ([0, 1], [0, 0])]

-- The count of the sites, round by round. No reference: the one round has nothing to replace.
#guard counts noRef = [0, 0]
#guard counts oneRef = [1, 0, 0]
-- The chain takes three rounds, one for each hop.
#guard counts chain = [3, 2, 1, 0, 0]
-- The diamond's count grows before it falls: six sites, nine after one round, none after two.
#guard counts diamond = [6, 9, 0, 0, 0, 0, 0, 0]
-- A round can leave the count as it is: the copy of the outer target brings its two sites.
#guard counts nestedTargets = [3, 3, 1, 0, 0]

#guard (noRef.expandRefs.refSites []).isEmpty && (oneRef.expandRefs.refSites []).isEmpty &&
  (chain.expandRefs.refSites []).isEmpty && (diamond.expandRefs.refSites []).isEmpty &&
  (nestedTargets.expandRefs.refSites []).isEmpty

-- The expansion holds the target's term at each site: the diamond's four leaves, three times.
#guard (Node.eff oneRef.expandRefs).layerAt [0, 1] = some leaf
#guard (Node.eff diamond.expandRefs).layerAt [0, 1, 1, 0] =
  some (.merge leaf (.merge leaf leaf))

/-- The theorem at the diamond: its premise is computed, and its conclusion is the guard above. -/
example : diamond.expandRefs.refSites [] = [] :=
  expanded_refs_nil_of_wf diamond (by decide +kernel)

/-- The theorem at the program with no reference: the same statement, at one round. -/
example : noRef.expandRefs.refSites [] = [] :=
  expanded_refs_nil_of_wf noRef (by decide +kernel)

/-! ## Red: each way that the references are refused -/

#guard !insideTarget.layerRefsWF && !forward.layerRefsWF && !refTarget.layerRefsWF &&
  !missing.layerRefsWF

-- Each control fails at its own clause, and at no other.
-- A reference inside its own target: the target precedes the site, and it encloses the site.
#guard clauses insideTarget = [(true, false, true)]
-- A forward reference: the target does not precede the site.
#guard clauses forward = [(false, true, true)]
-- A target that is a reference: the first site is well formed, and the second names it.
#guard clauses refTarget = [(true, true, true), (true, true, false)]
#guard (Node.eff refTarget).layerAt [0, 1, 0] = some (.ref [0, 0])
-- A missing target: the path would precede the site, and it names no layer.
#guard clauses missing = [(true, true, false)]
#guard (Node.eff missing).layerAt [0, 0, 5] = none

-- Without the premise the conclusion fails: the reference inside its own target stays at every
-- round, and so does the reference to a missing target.
#guard counts insideTarget = [1, 1, 1]
#guard counts missing = [1, 1, 1]
#guard insideTarget.expandRefs.refSites [] = [([0, 0, 0, 0], [0])]
#guard missing.expandRefs.refSites [] = [([0, 1], [0, 0, 5])]

/-- **Red** (proved): the premise of `expanded_refs_nil_of_wf` is needed. The program with a
reference inside its own target keeps a reference site after the rounds. -/
theorem insideTarget_keeps_reference : insideTarget.expandRefs.refSites [] ≠ [] := by
  decide +kernel

-- The premise is sufficient and not necessary: these two refused programs expand to a program
-- with no reference site all the same.
#guard counts forward = [1, 0, 0]
#guard counts refTarget = [2, 1, 0, 0]

/-! ## The consumers -/

/-- The native signature at the empty row table. -/
def sig : Signature NativeOp := nativeSignature []

-- The checker's equation, evaluated: on each of the nine programs the checker answers the
-- structural type of the expansion exactly when the references are well formed.
#guard programs.all fun p =>
  typeOfProgram sig p == if p.layerRefsWF then typeOf sig p.expandRefs else none

-- The five well-formed programs have a type, and the four refused programs have none.
#guard [noRef, oneRef, chain, diamond, nestedTargets].all fun p => (typeOfProgram sig p).isSome
#guard [insideTarget, forward, refTarget, missing].all fun p => (typeOfProgram sig p).isNone

-- `typeOfProgram_expandRefs`, evaluated on the five: the checker's answer on the expansion is its
-- answer on the program.
#guard [noRef, oneRef, chain, diamond, nestedTargets].all fun p =>
  typeOfProgram sig p.expandRefs == typeOfProgram sig p

/-- `typeOfProgram_expandRefs` at the diamond, with its one premise. -/
example : typeOfProgram sig diamond.expandRefs = typeOfProgram sig diamond :=
  typeOfProgram_expandRefs sig diamond (by decide +kernel)

/-- **Red** (proved): `typeOfProgram_expandRefs` keeps its premise. The checker refuses the
program with a forward reference, and it gives the program's expansion a type. -/
theorem forward_needs_wellFormed :
    typeOfProgram sig forward.expandRefs ≠ typeOfProgram sig forward := by
  decide +kernel

/-- The type that the checker gives the chain's expansion. -/
def chainTy : EffTy := EffTy.pure .nat

/-- `checkTypedProgram_of_hasTy` at the chain, from a declarative derivation on the expanded
tree and well-formed references: the caller owes no fact about the expansion's sites. -/
example : ∃ checked, checkTypedProgram sig chain = some checked ∧ checked.ty = chainTy :=
  checkTypedProgram_of_hasTy (by decide +kernel)
    (.plain (Conform.Effect4.Typing.effTy_sound sig chain.expandRefs [] chainTy (by decide +kernel)))

/-- The certificate's fact at the chain: the expansion has no reference site. The checker does
not test it, and the certificate takes it from `expanded_refs_nil_of_wf`. -/
example (checked : TypedProgram sig chain) : chain.expandRefs.refSites [] = [] :=
  checked.expanded_refSites

/-! ## One test: every answer as before

The checker tests the references' formation only, and the facade's refusal has no arm for a
reference site that the expansion keeps (decisions row 273, point 2). Each expected value below
is the answer of the tree before that change, measured at `git:8fcab517`. A red control beside a
check states that a different value is not the answer. -/

-- The checker's answer on the nine: one type for the five, and none for the four.
#guard [noRef, oneRef, chain, diamond, nestedTargets].all fun p =>
  typeOfProgram sig p == some (EffTy.pure .nat)
#guard [insideTarget, forward, refTarget, missing].all fun p => typeOfProgram sig p == none
-- Red: the five have the layer's carrier as their type, and no other.
#guard [noRef, oneRef, chain, diamond, nestedTargets].all fun p =>
  typeOfProgram sig p != some (EffTy.pure .unit)

-- The facade's verdict is the checker's, on the nine.
#guard programs.all fun p => Api.typeOf p == typeOfProgram sig p

-- The facade's refusal on the nine: none for the five, and the root refusal for the four.
#guard [noRef, oneRef, chain, diamond, nestedTargets].all fun p => Api.explain p == none
#guard [insideTarget, forward, refTarget, missing].all fun p =>
  Api.explain p == some ⟨[], .referencesIllFormed⟩
-- Red: two of the four keep a reference site in the expansion, and the facade does not refuse
-- there. The formation test refuses each at the root first.
#guard Api.explain insideTarget != some ⟨[0, 0, 0, 0], .layerReference [0]⟩
#guard Api.explain missing != some ⟨[0, 1], .layerReference [0, 0, 5]⟩

-- The tenth program: its one reference is well formed, and its expansion has no reference site.
#guard refusedBody.refSites [] = [([0, 1], [0, 0])]
#guard refusedBody.layerRefsWF && (refusedBody.expandRefs.refSites []).isEmpty
-- As written, the structural checker refuses at the reference: `layerReference` keeps its producer.
#guard Effect4.Program.explain sig [] refusedBody == some ⟨[0, 1], .layerReference [0, 0]⟩
-- The facade answers the structural refusal of the expansion: past the reference site, at the body.
#guard Api.explain refusedBody == some ⟨[1], .errorNotAdmitted .bool⟩
#guard Api.explain refusedBody == Effect4.Program.explain sig [] refusedBody.expandRefs
#guard typeOfProgram sig refusedBody == none
-- Red: the facade's refusal is not the refusal of the program as written.
#guard Api.explain refusedBody != Effect4.Program.explain sig [] refusedBody

/-- The facade's equation at the tenth program. The program is closed, so this instance reads the
branch that the program takes. The statement's pin below holds both branches. -/
example : Api.explain refusedBody =
    if refusedBody.layerRefsWF then Effect4.Program.explain sig [] refusedBody.expandRefs
    else some ⟨[], .referencesIllFormed⟩ :=
  Api.explain_eq_if_refsWF refusedBody []

/-- **No program is at the arm that the facade lost** (proved). The arm answered where the
references are well formed and the expansion keeps a reference site. So no program has a refusal
that came from that arm, and this battery can pin none. The premise is needed:
`insideTarget_keeps_reference` above. -/
example (program : NativeEff) (site : List Nat × List Nat) (rest : List (List Nat × List Nat))
    (wellFormed : program.layerRefsWF = true) :
    program.expandRefs.refSites [] ≠ site :: rest := by
  rw [expanded_refs_nil_of_wf program wellFormed]
  exact nofun

end Test.Program.ReferenceExpansion
