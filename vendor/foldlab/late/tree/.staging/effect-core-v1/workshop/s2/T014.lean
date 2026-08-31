import Cas.Core.Admission
import Cas.Backend.Canon
import Cas.Lang.Defun
import Cas.Lift.Decode

/-!
# Effect Core v1 — `EC1-T014`, slice `EC1-S2` (admission boundary)

Row under implementation: `EC1-T014 erase_wf : ProgramWF (erase p)`
(`PROOF-DAG.md:216`, `Depends on: T010,T013`).
Intended home, NOT written by this file:
`formal/effect-core-v1/EffectCore/Admission/Check.lean` (verified: still the
reserved empty boundary — a doc comment plus `namespace EffectCore.Admission`
/ `end`, no declarations).

Skill stage: `.claude/skills/lean/workflows/lean-model-invariants/SKILL.md`.
This row is a representation-layer question — raw/checked boundary, what the
carrier stores versus what a theorem must earn, and where the erasure lands —
so `lean-model-invariants` is the stage, not `lean-algebraic-systems`. Its
`references/boundaries-and-erasure.md` fixes the shape used below:
`raw -> parse -> validate -> checked core`, with an explicit projection back
to raw, validator soundness proved, completeness proved because rejection of
every valid input matters here (`EC1-T011`).

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s2/T014.lean
```

## What this file is

`EC1-D020 RawProgram`, `D021 ProgramWF`, `D022 Diagnostic`, `D023
CheckedProgram`, `D024 check`, `D025 erase` and `D026 normalizeRaw` are all
`PROPOSED TERM` rows (`PROOF-DAG.md:107-113`) with no Lean definition in the
tree. So this file BUILDS the minimum carrier `EC1-T014` needs, in the shape
the packet's own prose fixes, and proves the row against it.

The carrier is deliberately small — six clauses, not twelve — but it is not a
toy in the one respect that matters for this row: it has a real first-error
checker built by structural recursion over per-clause decidable reflection
(`PROOF-DAG.md:518`'s named route for the Checker family), whose soundness AND
completeness are proved, and `Block.body` is the estate's existing `PProg`
(`PROOF-DAG.md:118-121`: "Each proposed `Block` contains the existing `PProg`
as its sequential body"). Nothing is minted that the estate already owns.

A successful elaboration below proves the stated propositions and NOTHING
more. It is not model assurance, not implementation assurance, and it closes
no proof-DAG row.

## Checks omitted, stated up front

* Six of `ALGEBRA.md:297-318`'s twelve clauses are modelled; clauses 4-8 and 11
  (regions, handlers, resume, fibers, resources, `AERWF`) are NOT. Nothing here
  claims they are decidable, and the `AER` index is a stand-in (§4).
* No clause is proved undecidable. That is not expressible in Lean without a
  computability model, and every `Prop` is classically `Decidable`.
* `EC1-T006 normalizeRaw_idempotent` and `EC1-T007 normalizeRaw_alpha` are S1
  rows running concurrently in `workshop/s1/`, which this file did not read.
  Nothing below uses either: §9's route replaces idempotence with clause 12.
* `EC1-T015`, `EC1-T016`, `EC1-T017` are not addressed. `SynthAER` and
  `normalizeChecked` have no declaration node in the packet (grepped; see §4
  and §9), so no faithful model of them can be written today.
* Falsifiers `F01-F10`/`F81` (`PROOF-DAG.md` §15's stated `EC1-S2` exit) were
  not run — they have no carriers either.
* Nothing in `library/`, `formal/effect-core-v1/`, or any packet `.md` was
  modified, and no writing git command was run.

## Findings

| § | Question | Finding |
|---|---|---|
| 5 | Is `EC1-T014` a theorem? | It is the `wf` FIELD. Provable, and its proof term is `CheckedProgram.wf`. Neither stated dependency (`T010`, `T013`) can occur in it. |
| 6 | What is the content-bearing row? | `erase_readmitted`. Proved. It consumes `clauses_complete` (`T011`), never `T013`. |
| 7 | Is the DAG's `T014 <- T013` edge sound? | The route exists and buys nothing. `check_erase` (`T013`) is proved here through `clauses_complete` (`T011`), which the DAG lists as a dependency of neither — so the edge inverts a real dependency. |
| 8 | Design (b), `erase` normalizes? | `EC1-T014` is FALSE at this carrier. Witness: canonical block ordering moves the entry block. |
| 9 | `CONTRACT-PACKET.md:309`? | A projection, not a theorem — because canonicality is a `ProgramWF` clause. `normalizeChecked` is the identity and needs no declaration. |
| 10 | Is `ProgramWF : RawProgram -> Prop` well posed? | No. One clause is registry-relative; `EC1-D021` drops the index. |
-/

namespace EC1T014

open Cas Cas.Lang

/-! ## §1 — the carrier

`raw -> validate -> checked` with an explicit erasure, per the stage's
boundary shape. `Block.body` is the estate's `PProg`; no second straight-line
carrier is minted. -/

/-- The resolution environment: which foreign IDs resolve. The estate's
admission judgment is environment-indexed at `Cas/Core/Admission.lean:49`
(`checkRefs (σ : Store)`); `EC1-D021` is not. See §10. -/
structure Env where
  registry : List UInt8
  deriving DecidableEq

/-- Block terminators, cut to the two arms this row needs. -/
inductive Term where
  | close
  | jump (dst : Nat)
  deriving DecidableEq

/-- The successor block IDs a terminator names. -/
def Term.targets : Term → List Nat
  | .close => []
  | .jump d => [d]

/-- `EC1-A11 Block`: an ID, the existing `PProg` as sequential body, the
foreign IDs the block uses, and one terminator. -/
structure Block where
  id : Nat
  body : PProg
  foreign : List UInt8
  term : Term
  deriving DecidableEq

/-- `EC1-D020 RawProgram`. Duplicate IDs and dangling jumps are deliberately
REPRESENTABLE (`ALGEBRA.md:243-246`), which is what forces extrinsic typing
here rather than an indexed family. -/
structure RawProgram where
  entry : Nat
  blocks : List Block
  deriving DecidableEq

/-- The declared block IDs, in table order. -/
def blockIds (r : RawProgram) : List Nat := r.blocks.map Block.id

/-! ### The normalizer

`EC1-D026 normalizeRaw`. Canonical table ordering by block ID
(`PROOF-DAG.md:100-102` requires "canonical ordering/normalization for rows
and tables"). Written as hand-rolled insertion sort rather than
`List.mergeSort` so that it reduces in the kernel and `decide` can run it;
`Cas/Backend/Canon.lean`'s `mergeSort` family is the reason `EC1-CE030`'s
receipt carries `Classical.choice`, and this file carries none. -/

def insertById (b : Block) : List Block → List Block
  | [] => [b]
  | c :: rest => if b.id ≤ c.id then b :: c :: rest else c :: insertById b rest

def sortBlocks : List Block → List Block
  | [] => []
  | b :: rest => insertById b (sortBlocks rest)

def normalizeRaw (r : RawProgram) : RawProgram :=
  { r with blocks := sortBlocks r.blocks }

/-! ### The diagnostic

`EC1-D022 Diagnostic`. ONE first-error value carrying a payload, per `R16`
part 1 and `EC1-CE031`. The payload arms exist because a code-plus-path pair
provably cannot reconstruct a diagnostic at the estate's own family
(`AdmissionError.wrongKind` carries `expected` and `actual`); this file makes
no claim about WHICH payload is produced — every statement below quantifies
the diagnostic existentially, which is exactly `R16`'s admissible shape. -/
inductive Diagnostic where
  | ids (dup : Option Nat)
  | refs (bad : Option Nat)
  | lines (blk : Option Nat)
  | foreign (fid : Option UInt8)
  | entry (declared : Nat) (first : Option Nat)
  | canon
  deriving DecidableEq

/-! ## §2 — six clauses, each with its own decision and its own reflection

`PROOF-DAG.md:518` fixes this family's route: "structural recursion plus
decidable per-clause reflection", with "using successful examples as
completeness" named as the PROHIBITED shortcut. So every clause below gets

* a `Prop` defined independently of any checker, and
* a `Bool` defined by structural recursion, and
* an `_iff` tying them,

on the estate's own template `Cas/IR/Reach.lean:528/531/535`
(`reachB` / `reachB_sound` / `reachB_complete`). A bare `Decidable` instance
would not do: `EC1-T011` needs the completeness direction as a theorem, and a
`decide (ProgramWF r)` shortcut is exactly what collapses `EC1-T010` into a
projection.

Clause numbering follows `ALGEBRA.md:297-318` where it corresponds; the frozen
order is the order of §3's `clauseList`. -/

/-! ### Clause 1 — `IdsWF`: block IDs are duplicate-free -/

def nodupB : List Nat → Bool
  | [] => true
  | a :: as => !as.contains a && nodupB as

def NoDupIds : List Nat → Prop
  | [] => True
  | a :: as => a ∉ as ∧ NoDupIds as

theorem nodupB_iff : ∀ l : List Nat, nodupB l = true ↔ NoDupIds l
  | [] => by simp [nodupB, NoDupIds]
  | a :: as => by
      simp [nodupB, NoDupIds, nodupB_iff as]

def findDupId : List Nat → Option Nat
  | [] => none
  | a :: as => if as.contains a then some a else findDupId as

/-! ### Clause 2 — `RefsWF`: every jump target is a declared block

The half of `ALGEBRA.md:297` clause 1 that says "every reference resolves",
separated so the frozen order can put duplicate-freeness strictly first —
`EC1-CE030` / `R16` part 2 make a canonicality clause ill-founded before
`Nodup` is established, and the same discipline applies to resolution. -/

def refsB (r : RawProgram) : Bool :=
  r.blocks.all fun b => b.term.targets.all fun t => (blockIds r).contains t

def RefsWF (r : RawProgram) : Prop :=
  ∀ b ∈ r.blocks, ∀ t ∈ b.term.targets, t ∈ blockIds r

theorem refsB_iff (r : RawProgram) : refsB r = true ↔ RefsWF r := by
  simp [refsB, RefsWF, List.all_eq_true]

def findBadJump (r : RawProgram) : Option Nat :=
  r.blocks.findSome? fun b => b.term.targets.find? fun t => !(blockIds r).contains t

/-! ### Clause 3 — `LinesWF`: every code point is well formed

The estate's own line judgment `Cas/Lang/Defun.lean:191 PLine.WF` is reused
verbatim. It ships WITHOUT a decision procedure, so the reflection pair below
is the missing half of the route, not a new judgment. -/

def pinB : PIn → Bool
  | .lit _ => true
  | .ans i => decide (i < 4294967296)

theorem pinB_iff (i : PIn) : pinB i = true ↔ i.WF := by
  cases i <;> simp [pinB, PIn.WF]

def plineB : PLine → Bool
  | .put _ _ payload refs =>
      decide (payload.length < 4294967296) && decide (refs.length < 4294967296) &&
        refs.all fun r => pinB r.2
  | .load src => pinB src

theorem plineB_iff (l : PLine) : plineB l = true ↔ l.WF := by
  cases l with
  | put v t payload refs =>
      simp [plineB, PLine.WF, List.all_eq_true, pinB_iff, and_assoc]
  | load src => simpa [plineB, PLine.WF] using pinB_iff src

def linesB (r : RawProgram) : Bool := r.blocks.all fun b => b.body.all plineB

def LinesWF (r : RawProgram) : Prop := ∀ b ∈ r.blocks, ∀ l ∈ b.body, l.WF

theorem linesB_iff (r : RawProgram) : linesB r = true ↔ LinesWF r := by
  simp [linesB, LinesWF, List.all_eq_true, plineB_iff]

def findBadBlock (r : RawProgram) : Option Nat :=
  (r.blocks.find? fun b => !b.body.all plineB).map Block.id

/-! ### Clause 9 — `ForeignWF`: every foreign ID resolves in the registry

This is the environment-relative clause. `ALGEBRA.md:312` demands "every
foreign ID resolves to a registry entry"; the registry is not part of the raw
program, exactly as the `Store` is not part of a `List Ref` at
`Cas/Core/Admission.lean:49`. See §10. -/

def foreignB (rho : Env) (r : RawProgram) : Bool :=
  r.blocks.all fun b => b.foreign.all fun f => rho.registry.contains f

def ForeignWF (rho : Env) (r : RawProgram) : Prop :=
  ∀ b ∈ r.blocks, ∀ f ∈ b.foreign, f ∈ rho.registry

theorem foreignB_iff (rho : Env) (r : RawProgram) :
    foreignB rho r = true ↔ ForeignWF rho r := by
  simp [foreignB, ForeignWF, List.all_eq_true]

def findBadForeign (rho : Env) (r : RawProgram) : Option UInt8 :=
  r.blocks.findSome? fun b => b.foreign.find? fun f => !rho.registry.contains f

/-! ### Clause 10 — `EntryWF`: the entry is the first declared block

`ALGEBRA.md:315`'s entry clause, read SYNTACTICALLY and positionally. The
positional reading is not invented here: `EC1-CE040`'s `entryNotZero` witness
(VERIFIED-KERNEL) is precisely a graph that is denotationally equal to the
injected table and is refused because its entry is not at position zero. R4
("identity hashes presentations, never denotations") is what licenses a
presentation-sensitive clause. -/

def entryB (r : RawProgram) : Bool := decide ((blockIds r).head? = some r.entry)

def EntryWF (r : RawProgram) : Prop := (blockIds r).head? = some r.entry

theorem entryB_iff (r : RawProgram) : entryB r = true ↔ EntryWF r := by
  simp [entryB, EntryWF]

/-! ### Clause 12 — `CanonWF`: the raw program is already in normal form

`CONTRACT-PACKET.md:309` requires `erase checked = normalizeRaw (erase
checked)`. §9 shows that stating canonicality as a CLAUSE is what makes that
equation a projection instead of an unowned normalizer-preservation
obligation. -/

def canonB (r : RawProgram) : Bool := decide (normalizeRaw r = r)

def CanonWF (r : RawProgram) : Prop := normalizeRaw r = r

theorem canonB_iff (r : RawProgram) : canonB r = true ↔ CanonWF r := by
  simp [canonB, CanonWF]

/-! ## §3 — `ProgramWF`, and the first-error checker

`EC1-D021` is split in two on purpose.

`ProgramWFcore` is the raw-side judgment: the five clauses that say the graph
makes sense. `ProgramWF` adds canonicality. The split is not cosmetic — it is
the exact line along which §8's refutation runs, and §9's reading of
`CONTRACT-PACKET.md:309` depends on which side of it a design puts the
normalizer. -/

def ProgramWFcore (rho : Env) (r : RawProgram) : Prop :=
  NoDupIds (blockIds r) ∧ RefsWF r ∧ LinesWF r ∧ ForeignWF rho r ∧ EntryWF r

/-- `EC1-D021 ProgramWF`, environment-indexed (§10). -/
def ProgramWF (rho : Env) (r : RawProgram) : Prop :=
  ProgramWFcore rho r ∧ CanonWF r

/-! ### First-error sequencing

`R16` rules checker semantics FIRST-ERROR over one frozen clause order, and
`EC1-CE031` (VERIFIED-KERNEL) killed the per-condemning-clause reading. The
scan is factored out so the frozen order is a DECLARED object rather than an
emergent property of some checker's recursion — `EC1-T015`'s scout showed that
a checker-relative reading of "the first reject" makes its row the identity
function. -/

def firstError : List (Bool × Diagnostic) → Except Diagnostic Unit
  | [] => .ok ()
  | (b, d) :: rest => if b then firstError rest else .error d

theorem firstError_ok_iff :
    ∀ l : List (Bool × Diagnostic), firstError l = .ok () ↔ ∀ p ∈ l, p.1 = true
  | [] => by simp [firstError]
  | (b, d) :: rest => by
      cases b with
      | false => simp [firstError]
      | true => simp [firstError, firstError_ok_iff rest]

/-- The frozen clause order. Duplicate-freeness is strictly first (`EC1-CE030`
/ `R16` part 2: a canonicality clause evaluated before `Nodup` is established
is ill-founded), and canonicality is strictly last. -/
def clauseList (rho : Env) (r : RawProgram) : List (Bool × Diagnostic) :=
  [ (nodupB (blockIds r), .ids (findDupId (blockIds r)))
  , (refsB r,             .refs (findBadJump r))
  , (linesB r,            .lines (findBadBlock r))
  , (foreignB rho r,      .foreign (findBadForeign rho r))
  , (entryB r,            .entry r.entry (blockIds r).head?)
  , (canonB r,            .canon) ]

/-- `EC1-D024`'s clause layer: a total, computable, fail-fast scan. -/
def checkClauses (rho : Env) (r : RawProgram) : Except Diagnostic Unit :=
  firstError (clauseList rho r)

/-- Checker SOUNDNESS at the clause layer — `EC1-T010`'s real content. Six
independently defined reflection lemmas, composed. Note what this is NOT: it
is not `Subtype.property`, because `checkClauses` is defined without ever
mentioning `ProgramWF`. -/
theorem clauses_sound {rho : Env} {r : RawProgram}
    (h : checkClauses rho r = .ok ()) : ProgramWF rho r := by
  have h6 := (firstError_ok_iff (clauseList rho r)).mp h
  simp only [clauseList, List.forall_mem_cons] at h6
  obtain ⟨e1, e2, e3, e4, e5, e6, -⟩ := h6
  exact ⟨⟨(nodupB_iff _).mp e1, (refsB_iff _).mp e2, (linesB_iff _).mp e3,
          (foreignB_iff _ _).mp e4, (entryB_iff _).mp e5⟩, (canonB_iff _).mp e6⟩

/-- Checker COMPLETENESS at the clause layer — `EC1-T011`'s real content, and
the only premise §6's restated `EC1-T014` actually consumes. -/
theorem clauses_complete {rho : Env} {r : RawProgram}
    (h : ProgramWF rho r) : checkClauses rho r = .ok () := by
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩ := h
  refine (firstError_ok_iff (clauseList rho r)).mpr ?_
  simp only [clauseList, List.forall_mem_cons]
  exact ⟨(nodupB_iff _).mpr h1, (refsB_iff _).mpr h2, (linesB_iff _).mpr h3,
         (foreignB_iff _ _).mpr h4, (entryB_iff _).mpr h5, (canonB_iff _).mpr h6,
         by simp⟩

/-! ## §4 — the checked carrier, `check`, and `erase`

`ALGEBRA.md:319-320`: "`EC1-A13 CheckedProgram A E R` stores an erased raw
value, normalized lookup tables, and evidence of `ProgramWF`", echoed at
`REIFICATION-CHECKLIST.md:859`: "`CheckedProgram A E R = RawProgram plus
ProgramWF and synthesized A/E/R`". That sentence is the whole of §5's finding,
taken literally.

The `AER` index below is a deliberate MINIMUM. `SynthAER` has no `PROPOSED
TERM` node anywhere in the packet — verified here by grep: the only two
occurrences in `.staging/effect-core-v1/*.md` are inside the `EC1-T016` and
`EC1-T017` rows themselves (`PROOF-DAG.md:218-219`). So no faithful synthesizer
can be written today, and this file uses a stand-in that does no work in any
theorem below except to carry the `Sigma` index. `EC1-T016`/`EC1-T017` are NOT
addressed here. -/

abbrev AER := Nat

/-- Stand-in synthesizer. NOT a model of `SynthAER`; see above. -/
def synthAER (r : RawProgram) : AER := r.blocks.length

/-- `EC1-D023 CheckedProgram`, indexed by the environment it was admitted
against (§10) and by the synthesized index. -/
structure CheckedProgram (rho : Env) (aer : AER) where
  raw : RawProgram
  wf : ProgramWF rho raw
  aerOk : synthAER raw = aer

/-- `EC1-D025 erase`. Design (a): a projection. Design (b) — normalize on the
way out — is §8. -/
def erase {rho : Env} {aer : AER} (p : CheckedProgram rho aer) : RawProgram := p.raw

/-- `EC1-D024 check`. Partial by type, per `R15` / `EC1-CE033`: a total
`RawProgram -> CheckedProgram` has no error arm and could decide nothing. -/
def check (rho : Env) (r : RawProgram) :
    Except Diagnostic (Σ aer, CheckedProgram rho aer) :=
  match hc : checkClauses rho r with
  | .error d => .error d
  | .ok ()   => .ok ⟨synthAER r, ⟨r, clauses_sound hc, rfl⟩⟩

/-- `EC1-T010 check_sound`, at this carrier. It is `clauses_sound` — six
independently defined reflection lemmas composed — NOT the `wf` projection.
Contrast §5. -/
theorem check_sound {rho : Env} {r : RawProgram} {x : Σ aer, CheckedProgram rho aer}
    (h : check rho r = .ok x) : ProgramWF rho r := by
  unfold check at h
  split at h
  · exact nomatch h
  · rename_i hc; exact clauses_sound hc

/-- `EC1-T011 check_complete`, at this carrier, with the alphabet index BOUND.
The DAG row (`PROOF-DAG.md:213`) leaves `a` free; read universally it is false
as soon as `AER` has two inhabitants, and read existentially it says nothing
about the index. Here the index is named by `synthAER`, so the statement is
closed and says which index comes back. -/
theorem check_complete {rho : Env} {r : RawProgram} (h : ProgramWF rho r) :
    ∃ q : CheckedProgram rho (synthAER r), check rho r = .ok ⟨synthAER r, q⟩ := by
  have hc : checkClauses rho r = .ok () := clauses_complete h
  unfold check
  split
  · rename_i d hc'; rw [hc] at hc'; exact nomatch hc'
  · exact ⟨_, rfl⟩

/-! ### The carrier is inhabited, and the checker rejects by computation

`PROOF-DAG.md:518` names "using successful examples as completeness" as the
prohibited shortcut for the Checker family. The positive witness below is not
used as evidence of completeness — completeness is `clauses_complete`, proved
in §3 for every input. The witnesses exist so that §5's projection theorem is
not a statement about an empty type, and so that the negative direction is a
KERNEL REDUCTION to `false` rather than the absence of a positive example. -/

def demoEnv : Env := ⟨[7]⟩

/-- One block: id 0, a single well-formed load, one foreign ID that resolves,
terminating. -/
def demoRaw : RawProgram :=
  { entry := 0, blocks := [⟨0, [PLine.load (.ans 0)], [7], .close⟩] }

theorem demo_accepts : checkClauses demoEnv demoRaw = .ok () := rfl

def demoChecked : CheckedProgram demoEnv (synthAER demoRaw) :=
  ⟨demoRaw, clauses_sound demo_accepts, rfl⟩

/-- NEGATIVE 1: an out-of-range answer index. The line judgment is the
estate's own `PLine.WF`; the rejection is a kernel computation. -/
def badLineRaw : RawProgram :=
  { entry := 0, blocks := [⟨0, [PLine.load (.ans 4294967296)], [], .close⟩] }

theorem badLine_rejected : checkClauses demoEnv badLineRaw = .error (.lines (some 0)) :=
  rfl

theorem badLine_not_wf : ¬ ProgramWF demoEnv badLineRaw := by
  intro h
  have := clauses_complete h
  rw [badLine_rejected] at this
  exact nomatch this

/-- NEGATIVE 2: a foreign ID absent from the registry — the environment-relative
clause, refusing. -/
def badForeignRaw : RawProgram :=
  { entry := 0, blocks := [⟨0, [], [9], .close⟩] }

theorem badForeign_rejected :
    checkClauses demoEnv badForeignRaw = .error (.foreign (some 9)) := rfl

/-! ## §5 — `EC1-T014` exactly as the DAG writes it: the `wf` field

`PROOF-DAG.md:216` — `EC1-T014 erase_wf : ProgramWF (erase p)`, depending on
`T010,T013`. Under the carrier the packet's own prose fixes, it is provable
and its proof term is `CheckedProgram.wf`.

This is a DIFFERENT defect from the `exists!` tautologies `PROOF-DAG.md:203-205`
already deleted. The statement is not trivially true — an unsatisfiable
`ProgramWF` makes `CheckedProgram` uninhabited, which is why §4 exhibits a
witness. It is INFORMATION-FREE relative to the carrier definition, and its
two stated dependencies are not merely unnecessary but UNMENTIONABLE: nothing
in the statement can refer to a checker.

The estate already ruled on this shape and never wrote the row. `Node.WF` is
paired with a `Decidable` instance at `Cas/Core/Node.lean:47/50` and bundled as
`abbrev AdmittedNode := { n : Node // n.WF }` at `:56`; there is no theorem
`admittedNode_wf` anywhere in `library/cas` (grepped). Every consumer writes
`.property` inline — `Cas/Codec/NodeCodec.lean:68,291,292`. See §11. -/

/-- **`EC1-T014`, as written.** -/
theorem erase_wf {rho : Env} {aer : AER} (p : CheckedProgram rho aer) :
    ProgramWF rho (erase p) := p.wf

/-- The proof term IS the field selector. -/
theorem erase_wf_is_the_field :
    @erase_wf = fun _ _ p => CheckedProgram.wf p := rfl

/-! ### The same statement, with the checker removed entirely -/

/-- The carrier `ALGEBRA.md:319-320` describes, over an ARBITRARY predicate —
possibly undecidable, with no checker, no soundness theorem, no round trip. -/
structure Bundled (Raw : Type) (WF : Raw → Prop) where
  raw : Raw
  wf : WF raw

def eraseBundled {Raw : Type} {WF : Raw → Prop} (p : Bundled Raw WF) : Raw := p.raw

/-- `EC1-T014` holds with `T010` and `T013` not merely unproved but absent from
the language of the statement. -/
theorem erase_wf_needs_no_checker :
    ∀ {Raw : Type} {WF : Raw → Prop} (p : Bundled Raw WF), WF (eraseBundled p) :=
  fun p => p.wf

theorem erase_wf_needs_no_checker_is_the_field :
    @erase_wf_needs_no_checker = fun _ _ p => Bundled.wf p := rfl

/-- The distinction that keeps this honest: information-freeness is not
truth-by-emptiness. The carrier CAN be empty, and §4's `demoChecked` shows
this one is not. -/
theorem bundled_can_be_empty : ¬ Nonempty (Bundled Nat (fun _ => False)) :=
  fun h => h.elim fun q => q.wf

/-! ### `EC1-T010` and `EC1-T014` together pin no checker

The checker that refuses every input satisfies `EC1-T010` vacuously, and
`EC1-T014` is untouched by it. Only completeness excludes it — which is why
§6's restatement is the row worth keeping. -/

def rejectAll (rho : Env) (_r : RawProgram) :
    Except Diagnostic (Σ aer, CheckedProgram rho aer) := .error .canon

theorem rejectAll_is_sound {rho : Env} {r : RawProgram}
    {x : Σ aer, CheckedProgram rho aer} (h : rejectAll rho r = .ok x) :
    ProgramWF rho r := nomatch h

theorem rejectAll_is_not_complete :
    ¬ ∀ (rho : Env) (r : RawProgram), ProgramWF rho r →
        ∃ (aer : AER) (q : CheckedProgram rho aer), rejectAll rho r = .ok ⟨aer, q⟩ := by
  intro h
  obtain ⟨_, _, hq⟩ := h demoEnv demoRaw (clauses_sound demo_accepts)
  exact nomatch hq

/-! ## §6 — `EC1-T014` restated: the checker readmits its own erasure

The content-bearing statement in this neighbourhood. It cannot be stored in
the carrier, because it mentions `check`, and no field can contain a function
of the whole program space. Its route is `clauses_complete` — `EC1-T011` —
and NOT `EC1-T013`. -/

/-- **`EC1-T014` (recommended).** -/
theorem erase_readmitted {rho : Env} {aer : AER} (p : CheckedProgram rho aer) :
    ∃ q : CheckedProgram rho aer, check rho (erase p) = .ok ⟨aer, q⟩ := by
  obtain ⟨raw, wf, aerOk⟩ := p
  subst aerOk
  exact check_complete wf

/-- The restatement has CONTENT: `rejectAll` satisfies `EC1-T010` (§5) and
`EC1-T014`-as-written (it is the same field projection at the same carrier),
and it FAILS readmission. So the restated row genuinely excludes a checker the
DAG row admits. -/
theorem readmission_excludes_rejectAll :
    ¬ ∀ (aer : AER) (p : CheckedProgram demoEnv aer),
        ∃ q : CheckedProgram demoEnv aer, rejectAll demoEnv (erase p) = .ok ⟨aer, q⟩ := by
  intro h
  obtain ⟨_, hq⟩ := h (synthAER demoRaw) demoChecked
  exact nomatch hq

/-- **`EC1-T013 check_erase`**, at this carrier. Proved through
`clauses_complete` — the same premise `erase_readmitted` consumes, which is
the whole of §7's point — and STRONGER than the DAG row: the returned payload
is `p` itself, so `normalizeChecked` is the identity and needs no declaration.
See §9 for why. -/
theorem check_erase {rho : Env} {aer : AER} (p : CheckedProgram rho aer) :
    check rho (erase p) = .ok ⟨aer, p⟩ := by
  obtain ⟨raw, wf, aerOk⟩ := p
  subst aerOk
  have hc : checkClauses rho raw = .ok () := clauses_complete wf
  unfold check erase
  split
  · rename_i d hc'; rw [hc] at hc'; exact nomatch hc'
  · rfl

/-! ## §7 — the DAG's own route, and the inverted edge

`PROOF-DAG.md:216` routes `EC1-T014` through `T010` and `T013`. The route is
AVAILABLE — and it buys nothing.

The edge is also inverted. `EC1-T013` cannot be proved without first knowing
that `check (erase p)` does not error, which is exactly `EC1-T014`'s content
under completeness. `check_erase` above is proved through `clauses_complete`;
the DAG lists `T013`'s dependencies as `T006,T010` (`PROOF-DAG.md:215`), naming
neither `T011` nor `T014`. Taking the DAG's edges literally gives
`T013 <- T014 <- T013`. -/

theorem erase_wf_via_T010_and_T013 {rho : Env} {aer : AER} (p : CheckedProgram rho aer) :
    ProgramWF rho (erase p) := check_sound (check_erase p)

/-- Both routes deliver the same proof. `ProgramWF` is a `Prop`, so the extra
dependency edges cannot change what is delivered — they can only change what
must be proved first. -/
theorem the_two_routes_agree {rho : Env} {aer : AER} (p : CheckedProgram rho aer) :
    erase_wf p = erase_wf_via_T010_and_T013 p := rfl

/-! ## §8 — design (b): `erase` normalizes, and `EC1-T014` is FALSE

`CONTRACT-PACKET.md:309` requires `erase checked = normalizeRaw (erase
checked)`. There are exactly two ways to satisfy it, and the packet has not
recorded which it means:

* (a) store an already-normalized raw and project — §4-§7 above; or
* (b) store an arbitrary admitted raw and normalize on the way OUT.

Under (b), `EC1-T014` unfolds to `ProgramWF rho r -> ProgramWF rho
(normalizeRaw r)`. That is an INDEPENDENT obligation which no DAG row owns:
`EC1-T006 normalizeRaw_idempotent` (`PROOF-DAG.md:198`) gives idempotence of
the normalizer, not preservation of well-formedness. It is false here.

The witness is not a strawman normalizer. `normalizeRaw` is canonical table
ordering, which `PROOF-DAG.md:100-102` requires; the clause it breaks is the
POSITIONAL entry clause, whose estate warrant is `EC1-CE040`'s VERIFIED-KERNEL
`entryNotZero` witness — a graph denotationally equal to the injected table
that `toPProg` refuses because its entry is not at position zero. Canonical
ordering and positional entry are both licensed by `R4` (identity hashes
presentations); they simply do not commute, which is exactly what clause 12
`PresentationWF` exists to notice. -/

/-- Design (b)'s carrier: the raw side only, no canonicality clause. -/
structure CheckedB (rho : Env) where
  raw : RawProgram
  wf : ProgramWFcore rho raw

def eraseB {rho : Env} (p : CheckedB rho) : RawProgram := normalizeRaw p.raw

/-- Two blocks, entry declared and listed first, IDs out of canonical order. -/
def badOrderRaw : RawProgram :=
  { entry := 5, blocks := [⟨5, [], [], .close⟩, ⟨1, [], [], .close⟩] }

theorem badOrder_core : ProgramWFcore demoEnv badOrderRaw :=
  ⟨(nodupB_iff _).mp rfl, (refsB_iff _).mp rfl, (linesB_iff _).mp rfl,
   (foreignB_iff _ _).mp rfl, (entryB_iff _).mp rfl⟩

theorem badOrder_normalized_entryB_false : entryB (normalizeRaw badOrderRaw) = false := rfl

theorem badOrder_normalized_not_core : ¬ ProgramWFcore demoEnv (normalizeRaw badOrderRaw) := by
  intro h
  have hb := (entryB_iff (normalizeRaw badOrderRaw)).mpr h.2.2.2.2
  rw [badOrder_normalized_entryB_false] at hb
  exact Bool.noConfusion hb

/-- **`EC1-T014` under design (b) is FALSE.** -/
theorem erase_wf_designB_is_false :
    ¬ ∀ p : CheckedB demoEnv, ProgramWFcore demoEnv (eraseB p) := by
  intro h
  exact badOrder_normalized_not_core (h ⟨badOrderRaw, badOrder_core⟩)

/-- The obligation design (b) owes, named. No `PROOF-DAG.md` row states it. -/
def NormalizerPreservesWF (rho : Env) : Prop :=
  ∀ r : RawProgram, ProgramWFcore rho r → ProgramWFcore rho (normalizeRaw r)

theorem normalizer_does_not_preserve_wf : ¬ NormalizerPreservesWF demoEnv :=
  fun h => badOrder_normalized_not_core (h badOrderRaw badOrder_core)

/-! ## §9 — the resolution, and why `normalizeChecked` need not exist

Design (a) survives §8 for a reason that is worth stating as a design rule:
under (a) the erase-normal-form equation is discharged by a `ProgramWF`
CLAUSE, so no preservation lemma is needed anywhere. Concretely, the checker
of §3 REFUSES the very program that breaks design (b) — and refuses it at the
canonicality clause, by computation. -/

theorem badOrder_refused_by_the_canonical_checker :
    checkClauses demoEnv badOrderRaw = .error .canon := rfl

/-- `CONTRACT-PACKET.md:309`, `erase checked = normalizeRaw (erase checked)`.
`PROOF-DAG.md:212-219` has NO row for this equation. At this carrier it is a
projection of clause 12, not a theorem. -/
theorem erase_is_normal {rho : Env} {aer : AER} (p : CheckedProgram rho aer) :
    erase p = normalizeRaw (erase p) := p.wf.2.symm

theorem erase_is_normal_is_the_clause :
    @erase_is_normal = fun _ _ p => ((CheckedProgram.wf p).2).symm := rfl

/-- `CONTRACT-PACKET.md:310`, `check (erase checked) = ok (normalizeChecked
checked)`, with `normalizeChecked` = identity. `normalizeChecked` occurs
exactly twice in the packet (`PROOF-DAG.md:215`, `CONTRACT-PACKET.md:310`) and
has no `PROPOSED TERM` row; under design (a) it does not need one. -/
theorem normalizeChecked_is_the_identity {rho : Env} {aer : AER}
    (p : CheckedProgram rho aer) : check rho (erase p) = .ok ⟨aer, p⟩ := check_erase p

/-! ## §10 — `ProgramWF : RawProgram -> Prop` is under-specified

`PROOF-DAG.md:108` gives `ProgramWF : RawProgram -> Prop` and `:111` gives
`check : RawProgram -> Except Diagnostic (Sigma CheckedProgram)`; neither takes
an environment. But `ALGEBRA.md:312` `ForeignWF` demands "every foreign ID
resolves to a REGISTRY ENTRY", and the registry is not part of the raw
program — exactly as the `Store` is not part of a `List Ref` at
`Cas/Core/Admission.lean:49`, where the shipped judgment IS indexed
(`checkRefs (σ : Store)`, `checkRefs_ok_iff {σ : Store}` at `:60`).

The local-anchor lane recorded this as a WIDENING ("the judgment goes from
store-relative to program-relative"). It is not a widening. Without the index
the proposition changes truth value on the same input. -/

def emptyEnv : Env := ⟨[]⟩

theorem programWF_is_registry_relative :
    ∃ (rho rho' : Env) (r : RawProgram), ForeignWF rho r ∧ ¬ ForeignWF rho' r := by
  refine ⟨demoEnv, emptyEnv, demoRaw, (foreignB_iff _ _).mp rfl, ?_⟩
  intro h
  have hb : foreignB emptyEnv demoRaw = true := (foreignB_iff emptyEnv demoRaw).mpr h
  have h0 : foreignB emptyEnv demoRaw = false := rfl
  rw [h0] at hb
  exact Bool.noConfusion hb

/-- So `EC1-T014` must read `ProgramWF rho (erase p)` for the `rho` that `p`
was admitted against. It does NOT generalize over environments. -/
theorem erase_wf_does_not_generalize_over_environments :
    ¬ ∀ (aer : AER) (p : CheckedProgram demoEnv aer) (rho : Env),
        ProgramWF rho (erase p) := by
  intro h
  have hf : ForeignWF emptyEnv demoRaw :=
    (h (synthAER demoRaw) demoChecked emptyEnv).1.2.2.2.1
  have hb : foreignB emptyEnv demoRaw = true := (foreignB_iff emptyEnv demoRaw).mpr hf
  have h0 : foreignB emptyEnv demoRaw = false := rfl
  rw [h0] at hb
  exact Bool.noConfusion hb

/-! ## §11 — anchors, re-elaborated

Every estate declaration this file leans on, named and forced through the
elaborator. A name that did not resolve would fail the file. Line numbers were
checked by reading, not inferred. -/

section Anchors

/-- `Cas/Core/Node.lean:56`. **The estate's own instance of the `EC1-T014`
shape**, and its treatment IS the ruling: erase-well-formedness is a
projection consumed at use sites, never a theorem row. There is no
`admittedNode_wf` in `library/cas` (grepped); consumers write `.property`
inline, e.g. `Cas/Codec/NodeCodec.lean:68,291,292`. This anchor is not in any
lane report for `EC1-T014`. -/
theorem estate_admittedNode_erase_wf (n : Cas.AdmittedNode) : n.val.WF := n.property

/-- `Cas/Core/Node.lean:47/50`. The `WF` + `Decidable` pairing this file copies
for all six clauses. -/
def estate_node_wf_decidable (n : Cas.Node) : Decidable n.WF := inferInstance

/-- `Cas/Lift/Decode.lean:422` — `EC1-T014`'s REPORTED anchor, and
misattributed. Its shape is `decodeLift v = .ok l -> (every line of l is WF)`:
that is SOUNDNESS OF THE DOOR, i.e. `EC1-T010`'s direction (into the checked
side), not `EC1-T014`'s (out of it). -/
abbrev anchor_reported_T014 := @Cas.Lift.decodeLift_wf

/-- `Cas/Lang/Defun.lean:871` — the estate's genuine `EC1-T014`-SHAPED theorem:
what comes OUT of the erasure admits. It is a theorem precisely because it
lands at a DIFFERENT predicate (`Word.wf` of the emitted word) than the one the
input carried. That is the test `EC1-T014` fails. -/
abbrev anchor_true_T014_shape := @Cas.Lang.encodeProg_wf

/-- `Cas/Core/Admission.lean:60` — soundness and completeness in one iff, the
house shape §2's clause lemmas follow. -/
abbrev anchor_T010_T011 := @Cas.checkRefs_ok_iff

/-- `Cas/Core/Admission.lean:108` — first-error soundness (`R16` part 1). -/
abbrev anchor_first_error_sound := @Cas.checkRefs_error_condemns

/-- `Cas/Core/Admission.lean:137` — EXISTENTIAL rejection completeness, `R16`'s
admissible pair, already shipped. -/
abbrev anchor_rejection_complete := @Cas.checkRefs_complete

/-- `Cas/Lang/Defun.lean:998` — `EC1-T013`'s model, and it pays for its round
trip with two PREMISES (`hwf`, `hsep`) whose necessity is exhibited at
`:1014-1038`. §6's `check_erase` pays with clause 12 instead. -/
abbrev anchor_T013 := @Cas.Lang.decodeProg_encodeProg

/-- `Cas/Backend/Canon.lean:288` / `:376` — `EC1-CE030` / `R16` part 2: the
positive needs `Nodup`, the premise-free form is refuted. This is why §3's
frozen order puts duplicate-freeness first and canonicality last. -/
abbrev anchor_CE030_positive := @Cas.Backend.canonServices_perm_of_nodup_keys
abbrev anchor_CE030_negative := @Cas.Backend.canonServices_perm_premise_is_necessary

end Anchors

end EC1T014

/-! ## Kernel receipts

`#print axioms` on every theorem in the file. `Classical.choice` appears in
exactly three receipts, all of them ESTATE theorems re-elaborated unchanged
(`decodeLift_wf`, `canonServices_perm_of_nodup_keys`,
`canonServices_perm_premise_is_necessary`); it is inherited from `library/cas`
and introduced by nothing authored here. No `sorry`, no `axiom`, no
`native_decide`, and no `#eval` used as a claim. -/

-- §2 clause reflection
#print axioms EC1T014.nodupB_iff
#print axioms EC1T014.refsB_iff
#print axioms EC1T014.pinB_iff
#print axioms EC1T014.plineB_iff
#print axioms EC1T014.linesB_iff
#print axioms EC1T014.foreignB_iff
#print axioms EC1T014.entryB_iff
#print axioms EC1T014.canonB_iff

-- §3 first-error checker
#print axioms EC1T014.firstError_ok_iff
#print axioms EC1T014.clauses_sound
#print axioms EC1T014.clauses_complete

-- §4 carrier, EC1-T010, EC1-T011, witnesses
#print axioms EC1T014.check_sound
#print axioms EC1T014.check_complete
#print axioms EC1T014.demo_accepts
#print axioms EC1T014.badLine_rejected
#print axioms EC1T014.badLine_not_wf
#print axioms EC1T014.badForeign_rejected

-- §5 EC1-T014 as written
#print axioms EC1T014.erase_wf
#print axioms EC1T014.erase_wf_is_the_field
#print axioms EC1T014.erase_wf_needs_no_checker
#print axioms EC1T014.erase_wf_needs_no_checker_is_the_field
#print axioms EC1T014.bundled_can_be_empty
#print axioms EC1T014.rejectAll_is_sound
#print axioms EC1T014.rejectAll_is_not_complete

-- §6 EC1-T014 restated
#print axioms EC1T014.erase_readmitted
#print axioms EC1T014.readmission_excludes_rejectAll
#print axioms EC1T014.check_erase

-- §7 the DAG's route
#print axioms EC1T014.erase_wf_via_T010_and_T013
#print axioms EC1T014.the_two_routes_agree

-- §8 design (b) refuted
#print axioms EC1T014.badOrder_core
#print axioms EC1T014.badOrder_normalized_entryB_false
#print axioms EC1T014.badOrder_normalized_not_core
#print axioms EC1T014.erase_wf_designB_is_false
#print axioms EC1T014.normalizer_does_not_preserve_wf

-- §9 the contract equations
#print axioms EC1T014.badOrder_refused_by_the_canonical_checker
#print axioms EC1T014.erase_is_normal
#print axioms EC1T014.erase_is_normal_is_the_clause
#print axioms EC1T014.normalizeChecked_is_the_identity

-- §10 environment relativity
#print axioms EC1T014.programWF_is_registry_relative
#print axioms EC1T014.erase_wf_does_not_generalize_over_environments

-- §11 anchors
#print axioms EC1T014.estate_admittedNode_erase_wf
#print axioms EC1T014.anchor_reported_T014
#print axioms EC1T014.anchor_true_T014_shape
#print axioms EC1T014.anchor_T010_T011
#print axioms EC1T014.anchor_first_error_sound
#print axioms EC1T014.anchor_rejection_complete
#print axioms EC1T014.anchor_T013
#print axioms EC1T014.anchor_CE030_positive
#print axioms EC1T014.anchor_CE030_negative
