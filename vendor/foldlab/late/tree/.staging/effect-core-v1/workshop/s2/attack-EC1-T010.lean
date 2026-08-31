import Cas.Lang.Defun

/-!
# Effect Core v1 — `EC1-T010` (`check_sound`), slice `EC1-S2`

Implementation probe for one proof-DAG row:

```
EC1-T010  check_sound : check r = ok <a,p> -> ProgramWF r        deps D0-D3
```

Written 2026-08-31 against the working tree, Lean `leanprover/lean4:v4.33.1`.
Skill stage: `lean-algebraic-systems` (a checker is an INTERPRETER over a
reified first-order program — semantic artifact 5 in that stage's list; proof
route "pure recursive interpreter/fold -> structural induction plus simp
lemmas for constructors", which is also `PROOF-DAG.md` §16's Checker route,
"structural recursion plus decidable per-clause reflection").

Run it:

```
cd library/cas
lake env lean ../../.staging/effect-core-v1/workshop/s2/T010.lean
```

Nothing here is proposed for `library/` or for
`formal/effect-core-v1/EffectCore/Admission/Check.lean`, which is still the
reserved empty scaffold. This file is a MINIMAL PACKET-LOCAL MODEL of the
admission boundary, built only so that `EC1-T010` has something to be true of.
It is not `EC1-D020`.

## What is proved, and what that is worth

| § | Statement | Force |
|---|---|---|
| 3 | twelve `*B_iff` lemmas | Decidable per-clause reflection. One `Prop`, one `Bool` that does not mention it, one lemma. |
| 4 | `clauses_sound` | **The row's content.** The twelve reflections composed by first-error `Except` sequencing over a frozen clause table. |
| 4 | `clauses_complete` | The converse. Owed with the row: it is what makes the checker a DECISION procedure, and it is `EC1-T011` at this carrier. |
| 4 | `decidableProgramWF` | Decidability is a CONSEQUENCE of `T010 ∧ T011`, not the dependency `PROOF-DAG.md:214` lists. Constructed, `[propext]` only. |
| 5 | `check_sound` | **`EC1-T010` itself**, at this carrier. `check_complete` and `check_error_iff` come with it. |
| 6 | `evidence_carrier_makes_T010_a_projection` | The row is DISCHARGED BY THE CARRIER, with no checker at all, if `CheckedProgram` stores `ProgramWF` evidence as a field (`ALGEBRA.md:319-320`). This file therefore does NOT store it. |
| 7 | `normalize_then_check_cannot_prove_T010` | A checker that normalizes before it decides proves nothing about its raw input. `EC1-CE030`/`R16` part 2, re-proved at this carrier with no `Classical.choice`. |
| 7 | `check_accepts_a_nondegenerate_program` | The twelve clauses are jointly satisfiable on a four-block program with a scope, a handled `perform`, a foreign call, a cycle, two escaping failures and a non-empty `PProg` body — so `clauses_complete` is not carried by a degenerate witness. |
| 8 | `presentation_follows_from_ids` | Clause 12 is DERIVABLE from clause 1 here. The twelve clauses are not independent. |
| 8 | `declared_reading_is_strictly_stronger` | Clause 5's declared-block reading rejects a program graph reachability would admit. Sound and conservative, and stated in `ProgramWF` so `T011` survives it. |

Axiom ceiling: the receipts at the foot. No `sorry`, no `axiom`, no
`native_decide`, no `#eval` carrying a claim, and no `Classical.choice`.

## Reuse

`PProg` (`Cas/Lang/Defun.lean:187`) is the block body, as `PROOF-DAG.md:121-123`
directs ("Each proposed `Block` contains the existing `PProg` as its sequential
body"). No second straight-line carrier is minted. Nothing else is imported:
the twelve clauses are stated over this file's own graph vocabulary because
`EC1-D020` does not exist yet.
-/

namespace EffectCoreT010

/-! ## §1 — list vocabulary

Local, first-order, and self-contained. `library/cas` carries no Mathlib, so
`∃!` does not parse and the `List.Nodup` API is not leaned on. -/

/-- Membership as a `Bool`, spelled locally so no `List.contains`/`List.elem`
naming churn reaches this file. -/
def memB {α : Type} [DecidableEq α] (x : α) : List α → Bool
  | [] => false
  | y :: t => decide (x = y) || memB x t

theorem memB_iff {α : Type} [DecidableEq α] (x : α) (l : List α) :
    memB x l = true ↔ x ∈ l := by
  induction l with
  | nil => simp [memB]
  | cons y t ih => simp [memB, ih]

theorem memB_eq_false_iff {α : Type} [DecidableEq α] (x : α) (l : List α) :
    memB x l = false ↔ x ∉ l := by
  rw [← Bool.not_eq_true, memB_iff]

/-- Duplicate-freeness. -/
def Distinct {α : Type} [DecidableEq α] : List α → Prop
  | [] => True
  | x :: xs => x ∉ xs ∧ Distinct xs

def distinctB {α : Type} [DecidableEq α] : List α → Bool
  | [] => true
  | x :: xs => !(memB x xs) && distinctB xs

theorem distinctB_iff {α : Type} [DecidableEq α] (xs : List α) :
    distinctB xs = true ↔ Distinct xs := by
  induction xs with
  | nil => simp [distinctB, Distinct]
  | cons x xs ih => simp [distinctB, Distinct, memB_eq_false_iff, ih]

/-- Strictly ascending: the canonical spelling of a row. Strict ascent already
carries duplicate-freeness, so one predicate does the work `ALGEBRA.md`'s
"rows are canonical" asks of two. -/
def Ascending : List Nat → Prop
  | [] => True
  | x :: t => (∀ y ∈ t, x < y) ∧ Ascending t

def ascendingB : List Nat → Bool
  | [] => true
  | x :: t => t.all (fun y => decide (x < y)) && ascendingB t

theorem ascendingB_iff (l : List Nat) : ascendingB l = true ↔ Ascending l := by
  induction l with
  | nil => simp [ascendingB, Ascending]
  | cons x t ih => simp [ascendingB, Ascending, ih]

/-- Ordered insertion with dedup. -/
def insAsc (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: t => if x < y then x :: y :: t else if x = y then y :: t else y :: insAsc x t

/-- Row canonicalization. -/
def ascend : List Nat → List Nat
  | [] => []
  | x :: t => insAsc x (ascend t)

/-- Concat-map, spelled locally so no `List.flatMap`/`List.join` naming churn
reaches this file. -/
def concatMap {α : Type} (f : α → List Nat) : List α → List Nat
  | [] => []
  | x :: xs => f x ++ concatMap f xs

/-- Keep-LAST dedup by key. This is the normalizer's engine, and keeping the
LAST occurrence is what makes normalization visible to a reference-resolution
map that reads the FIRST -- see §8 and §9. -/
def dedupLastBy {α : Type} (key : α → Nat) : List α → List α
  | [] => []
  | x :: xs => if memB (key x) (xs.map key) then dedupLastBy key xs else x :: dedupLastBy key xs

theorem dedupLast_keys_sub {α : Type} (key : α → Nat) (xs : List α) {k : Nat}
    (h : k ∈ (dedupLastBy key xs).map key) : k ∈ xs.map key := by
  induction xs with
  | nil => simp [dedupLastBy] at h
  | cons x xs ih =>
    rw [dedupLastBy] at h
    split at h
    · exact List.mem_cons_of_mem _ (ih h)
    · rw [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · rw [List.map_cons, List.mem_cons]; exact Or.inl h
      · exact List.mem_cons_of_mem _ (ih h)

/-- Normalization ESTABLISHES duplicate-freeness of keys, whatever the input
was. This is the fact that makes normalize-then-check unsound for `EC1-T010`. -/
theorem dedupLast_keys_distinct {α : Type} (key : α → Nat) (xs : List α) :
    Distinct ((dedupLastBy key xs).map key) := by
  induction xs with
  | nil => exact trivial
  | cons x xs ih =>
    rw [dedupLastBy]
    split
    · exact ih
    · next hc =>
      rw [List.map_cons]
      refine ⟨?_, ih⟩
      intro hmem
      exact hc ((memB_iff _ _).mpr (dedupLast_keys_sub key xs hmem))

/-- A one-sided `Option` quantifier, so the clause Props below never carry a
bare `match` past their own helper lemma. -/
def OptAll (o : Option Nat) (P : Nat → Prop) : Prop := ∀ d, o = some d → P d

def optAllB (o : Option Nat) (f : Nat → Bool) : Bool :=
  match o with
  | none => true
  | some d => f d

theorem optAllB_iff {o : Option Nat} {f : Nat → Bool} {P : Nat → Prop}
    (h : ∀ d, f d = true ↔ P d) : optAllB o f = true ↔ OptAll o P := by
  cases o with
  | none => simp [optAllB, OptAll]
  | some d => simp [optAllB, OptAll, h d]


/-! ## §2 — the carrier

A minimal first-order `RawProgram`. Every id and every value type is a `Nat`
tag with decidable equality; the block body is the estate's `PProg`, per
`PROOF-DAG.md:121-123`. This is a MODEL of `EC1-D020`, not `EC1-D020`: the
packet's row is prose and `formal/effect-core-v1/EffectCore/Admission/Check.lean`
is empty. Everything below is stated so the abstraction is visible.

An `Exit` whose `dest` is `none` LEAVES THE GRAPH. That is the syntactic
reading of "escaped" that clause 3 needs, and it is written into the carrier
rather than left to the checker. -/

open Cas.Lang in
/-- One exit edge of a terminator. `label` is the resume token, `fail` the
typed failure alternative the edge carries (`none` = the normal edge), `dest`
the destination block (`none` = the edge escapes the graph), `carry` the value
types the edge supplies to its destination. -/
structure Exit where
  label : Nat
  fail  : Option Nat
  dest  : Option Nat
  carry : List Nat
  deriving DecidableEq

/-- Terminators. `close` returns; `perform` runs a general operation; `foreign`
calls a registered foreign operation; `scope` enters a nested region. -/
inductive Term where
  | close   (ty : Nat)
  | perform (op : Nat) (exits : List Exit)
  | foreign (fid : Nat) (exits : List Exit)
  | scope   (child : Nat) (exits : List Exit)
  deriving DecidableEq

def Term.exits : Term → List Exit
  | .close _ => []
  | .perform _ es => es
  | .foreign _ es => es
  | .scope _ es => es

def Term.performedOp : Term → Option Nat
  | .perform o _ => some o
  | _ => none

open Cas.Lang in
/-- A block: the estate's `PProg` as its sequential body, plus parameters,
region, and terminator. -/
structure Block where
  id     : Nat
  params : List Nat
  region : Nat
  body   : PProg
  term   : Term
  deriving DecidableEq

/-- The alphabet row for one general operation: what it may raise and what it
requires. -/
structure OpDecl where
  op   : Nat
  errs : List Nat
  reqs : List Nat
  deriving DecidableEq

/-- One row of the closed foreign registry. -/
structure ForeignDecl where
  fid  : Nat
  req  : Nat
  errs : List Nat
  deriving DecidableEq

/-- One direct-handler clause: which block handles which operation. -/
structure HandlerClause where
  op  : Nat
  blk : Nat
  deriving DecidableEq

/-- Region nesting, given by a parent link. -/
structure RegionDecl where
  rid    : Nat
  parent : Option Nat
  deriving DecidableEq

/-- The `A/E/R` triple. `E` and `R` are keyed rows. -/
structure AER where
  A : Nat
  E : List Nat
  R : List Nat
  deriving DecidableEq

/-- The raw, UNCHECKED program. Duplicate identifiers, dangling references and
non-canonical rows are deliberately representable (`ALGEBRA.md:240-243`). -/
structure RawProgram where
  blocks   : List Block
  ops      : List OpDecl
  foreigns : List ForeignDecl
  handlers : List HandlerClause
  regions  : List RegionDecl
  entry    : Nat
  entryTy  : Nat
  resultTy : Nat
  declared : AER
  deriving DecidableEq

namespace RawProgram

/-- Reference resolution reads the FIRST matching row. This is the resolver
clause 12 compares before and after normalization. -/
def blockOf (r : RawProgram) (b : Nat) : Option Block := r.blocks.find? (fun x => x.id = b)
def opOf (r : RawProgram) (o : Nat) : Option OpDecl := r.ops.find? (fun x => x.op = o)
def foreignOf (r : RawProgram) (f : Nat) : Option ForeignDecl :=
  r.foreigns.find? (fun x => x.fid = f)
def regionOf (r : RawProgram) (g : Nat) : Option RegionDecl :=
  r.regions.find? (fun x => x.rid = g)
def handlersFor (r : RawProgram) (o : Nat) : List HandlerClause :=
  r.handlers.filter (fun x => x.op = o)

end RawProgram

/-! ## §3 — the twelve clauses

`ALGEBRA.md:295-317` names twelve. Each gets, separately:

* a `Prop`, written in ordinary quantifier form and NEVER as `f r = true`;
* a `Bool`, an explicit computation that does NOT mention the `Prop`;
* a reflection lemma tying the two.

The four semantic words in the packet's prose are pinned SYNTACTICALLY here,
in the clause itself and not merely in its decision procedure. `EC1-T010`
survives an approximation made only in `check`; `EC1-T011` does not (that is
the `strict_strengthening_kills_complete` result the T010 scout returned), so
the syntactic reading has to live in `ProgramWF`.

* "escaped" (clause 3) = the edge names no destination;
* "reachable" (clause 5) = DECLARED. Strictly stronger than graph-reachable,
  hence sound and conservative; see §9 for the exhibit that it is STRICTLY
  stronger, and `divergenceFromDag`;
* "do not escape / cannot outlive" (clauses 4, 7, 8) = containment in the
  region index order, which the acyclicity clause makes a real order;
* "meaning" (clause 12) = equality of the reference-resolution map before and
  after `normalizeRaw`. Never `SemEq`. -/

/-! ### clause 1 — `IdsWF` -/

def DestOk (r : RawProgram) (e : Exit) : Prop := OptAll e.dest (fun d => ∃ b, r.blockOf d = some b)
def destOkB (r : RawProgram) (e : Exit) : Bool := optAllB e.dest (fun d => (r.blockOf d).isSome)

theorem destOkB_iff (r : RawProgram) (e : Exit) : destOkB r e = true ↔ DestOk r e := by
  refine optAllB_iff ?_
  intro d
  cases h : r.blockOf d <;> simp

def TermRefsOk (r : RawProgram) : Term → Prop
  | .close _ => True
  | .perform o _ => ∃ d, r.opOf o = some d
  | .foreign f _ => ∃ d, r.foreignOf f = some d
  | .scope c _ => ∃ b, r.blockOf c = some b

def termRefsOkB (r : RawProgram) : Term → Bool
  | .close _ => true
  | .perform o _ => (r.opOf o).isSome
  | .foreign f _ => (r.foreignOf f).isSome
  | .scope c _ => (r.blockOf c).isSome

theorem termRefsOkB_iff (r : RawProgram) (t : Term) :
    termRefsOkB r t = true ↔ TermRefsOk r t := by
  cases t with
  | close ty => simp [termRefsOkB, TermRefsOk]
  | perform o es => cases h : r.opOf o <;> simp [termRefsOkB, TermRefsOk, h]
  | foreign f es => cases h : r.foreignOf f <;> simp [termRefsOkB, TermRefsOk, h]
  | scope c es => cases h : r.blockOf c <;> simp [termRefsOkB, TermRefsOk, h]

/-- Clause 1: every table is duplicate-free and every reference resolves. -/
def IdsWF (r : RawProgram) : Prop :=
  Distinct (r.blocks.map (·.id)) ∧ Distinct (r.ops.map (·.op)) ∧
  Distinct (r.foreigns.map (·.fid)) ∧ Distinct (r.handlers.map (·.op)) ∧
  Distinct (r.regions.map (·.rid)) ∧
  ∀ b ∈ r.blocks, TermRefsOk r b.term ∧ (∀ e ∈ b.term.exits, DestOk r e) ∧
    (∃ d, r.regionOf b.region = some d)

def idsB (r : RawProgram) : Bool :=
  distinctB (r.blocks.map (·.id)) && distinctB (r.ops.map (·.op)) &&
  distinctB (r.foreigns.map (·.fid)) && distinctB (r.handlers.map (·.op)) &&
  distinctB (r.regions.map (·.rid)) &&
  r.blocks.all (fun b => termRefsOkB r b.term && b.term.exits.all (destOkB r) &&
    (r.regionOf b.region).isSome)

theorem idsB_iff (r : RawProgram) : idsB r = true ↔ IdsWF r := by
  have hreg : ∀ b : Block, ((r.regionOf b.region).isSome = true) ↔ (∃ d, r.regionOf b.region = some d) := by
    intro b; cases h : r.regionOf b.region <;> simp
  simp [idsB, IdsWF, distinctB_iff, termRefsOkB_iff, destOkB_iff, hreg, and_assoc]

/-! ### clause 2 — `TypesWF` -/

/-- Clause 2: an exit's carried types agree EXACTLY with its destination's
parameters. -/
def TypesOk (r : RawProgram) (e : Exit) : Prop :=
  OptAll e.dest (fun d => ∀ tb, r.blockOf d = some tb → e.carry = tb.params)

def typesOkB (r : RawProgram) (e : Exit) : Bool :=
  optAllB e.dest (fun d => match r.blockOf d with
                           | none => true
                           | some tb => decide (e.carry = tb.params))

theorem typesOkB_iff (r : RawProgram) (e : Exit) : typesOkB r e = true ↔ TypesOk r e := by
  refine optAllB_iff ?_
  intro d
  cases h : r.blockOf d <;> simp

def TypesWF (r : RawProgram) : Prop := ∀ b ∈ r.blocks, ∀ e ∈ b.term.exits, TypesOk r e
def typesB (r : RawProgram) : Bool := r.blocks.all (fun b => b.term.exits.all (typesOkB r))

theorem typesB_iff (r : RawProgram) : typesB r = true ↔ TypesWF r := by
  simp [typesB, TypesWF, typesOkB_iff]

/-! ### clause 3 — `RowsWFsyn` -/

/-- The typed failure alternative this edge lets ESCAPE the graph, if any.
Syntactic: an edge escapes exactly when it names no destination. -/
def Exit.escapes (e : Exit) : Option Nat :=
  match e.dest with
  | none => e.fail
  | some _ => none

/-- Clause 3: rows are canonical, and every ESCAPED typed failure is in `E`. -/
def RowsWFsyn (r : RawProgram) : Prop :=
  Ascending r.declared.E ∧ Ascending r.declared.R ∧
  ∀ b ∈ r.blocks, ∀ e ∈ b.term.exits, OptAll e.escapes (fun x => x ∈ r.declared.E)

def rowsB (r : RawProgram) : Bool :=
  ascendingB r.declared.E && ascendingB r.declared.R &&
  r.blocks.all (fun b => b.term.exits.all (fun e => optAllB e.escapes (fun x => memB x r.declared.E)))

theorem rowsB_iff (r : RawProgram) : rowsB r = true ↔ RowsWFsyn r := by
  have h : ∀ e : Exit, (optAllB e.escapes (fun x => memB x r.declared.E) = true)
      ↔ OptAll e.escapes (fun x => x ∈ r.declared.E) :=
    fun e => optAllB_iff (fun d => memB_iff d r.declared.E)
  simp [rowsB, RowsWFsyn, ascendingB_iff, h, and_assoc]

/-! ### clause 4 — `RegionsWFsyn` -/

/-- Region nesting is acyclic BY CONSTRUCTION: a parent link points strictly
downwards in the region index order. -/
def RegionAcyclic (d : RegionDecl) : Prop := OptAll d.parent (fun p => p < d.rid)
def regionAcyclicB (d : RegionDecl) : Bool := optAllB d.parent (fun p => decide (p < d.rid))

theorem regionAcyclicB_iff (d : RegionDecl) : regionAcyclicB d = true ↔ RegionAcyclic d :=
  optAllB_iff (fun p => by simp)

/-- Every non-returning terminator routes somewhere. -/
def ExitRouting : Term → Prop
  | .close _ => True
  | .perform _ es => es ≠ []
  | .foreign _ es => es ≠ []
  | .scope _ es => es ≠ []

def exitRoutingB : Term → Bool
  | .close _ => true
  | .perform _ es => !es.isEmpty
  | .foreign _ es => !es.isEmpty
  | .scope _ es => !es.isEmpty

theorem exitRoutingB_iff (t : Term) : exitRoutingB t = true ↔ ExitRouting t := by
  cases t with
  | close ty => simp [exitRoutingB, ExitRouting]
  | perform o es => cases es <;> simp [exitRoutingB, ExitRouting]
  | foreign f es => cases es <;> simp [exitRoutingB, ExitRouting]
  | scope c es => cases es <;> simp [exitRoutingB, ExitRouting]

/-- Clause 4: region nesting is acyclic and every scoped body has complete exit
routing. -/
def RegionsWFsyn (r : RawProgram) : Prop :=
  (∀ d ∈ r.regions, RegionAcyclic d) ∧ (∀ b ∈ r.blocks, ExitRouting b.term)

def regionsB (r : RawProgram) : Bool :=
  r.regions.all regionAcyclicB && r.blocks.all (fun b => exitRoutingB b.term)

theorem regionsB_iff (r : RawProgram) : regionsB r = true ↔ RegionsWFsyn r := by
  simp [regionsB, RegionsWFsyn, regionAcyclicB_iff, exitRoutingB_iff]

/-! ### clause 5 — `HandlersWFsyn` -/

/-- Clause 5: exactly one typed clause for every operation performed by a
DECLARED block, and every handler clause resolves.

This is the conservative reading. Graph reachability is strictly smaller, so
demanding a clause for every declared `perform` is STRICTLY STRONGER — sound
for `EC1-T010`, and (unlike an approximation made only in `check`) compatible
with `EC1-T011`, because the strengthening is written into the clause itself.
§9 exhibits a program the strengthening rejects that graph reachability would
admit. -/
def HandlersWFsyn (r : RawProgram) : Prop :=
  (∀ b ∈ r.blocks, OptAll b.term.performedOp (fun o => (r.handlersFor o).length = 1)) ∧
  (∀ h ∈ r.handlers, ∃ b, r.blockOf h.blk = some b)

def handlersB (r : RawProgram) : Bool :=
  r.blocks.all (fun b => optAllB b.term.performedOp
      (fun o => decide ((r.handlersFor o).length = 1))) &&
  r.handlers.all (fun h => (r.blockOf h.blk).isSome)

theorem handlersB_iff (r : RawProgram) : handlersB r = true ↔ HandlersWFsyn r := by
  have h1 : ∀ b : Block, (optAllB b.term.performedOp
      (fun o => decide ((r.handlersFor o).length = 1)) = true)
      ↔ OptAll b.term.performedOp (fun o => (r.handlersFor o).length = 1) :=
    fun b => optAllB_iff (fun o => by simp)
  have h2 : ∀ h : HandlerClause, ((r.blockOf h.blk).isSome = true) ↔ (∃ b, r.blockOf h.blk = some b) := by
    intro h; cases hb : r.blockOf h.blk <;> simp
  simp [handlersB, HandlersWFsyn, h1, h2]

/-! ### clause 6 — `ResumeWF` -/

/-- Clause 6: within a SINGLE transition, resume labels are distinct — one
syntactic owner, no duplicate consumption path. The scoping phrase "within a
single transition" is load-bearing and is what keeps the clause decidable. -/
def ResumeWF (r : RawProgram) : Prop := ∀ b ∈ r.blocks, Distinct (b.term.exits.map (·.label))
def resumeB (r : RawProgram) : Bool := r.blocks.all (fun b => distinctB (b.term.exits.map (·.label)))

theorem resumeB_iff (r : RawProgram) : resumeB r = true ↔ ResumeWF r := by
  simp [resumeB, ResumeWF, distinctB_iff]

/-! ### clause 7 — `FibersWFsyn` -/

/-- Clause 7: control may move OUTWARD or stay, never inward — a scoped handle
cannot outlive its supervisor. Read as containment in the region index order,
which clause 4's acyclicity makes a real order. Never a property of runs. -/
def FiberOk (r : RawProgram) (owner : Nat) (e : Exit) : Prop :=
  OptAll e.dest (fun d => ∀ tb, r.blockOf d = some tb → tb.region ≤ owner)

def fiberOkB (r : RawProgram) (owner : Nat) (e : Exit) : Bool :=
  optAllB e.dest (fun d => match r.blockOf d with
                           | none => true
                           | some tb => decide (tb.region ≤ owner))

theorem fiberOkB_iff (r : RawProgram) (owner : Nat) (e : Exit) :
    fiberOkB r owner e = true ↔ FiberOk r owner e := by
  refine optAllB_iff ?_
  intro d
  cases h : r.blockOf d <;> simp

def FibersWFsyn (r : RawProgram) : Prop :=
  ∀ b ∈ r.blocks, ∀ e ∈ b.term.exits, FiberOk r b.region e

def fibersB (r : RawProgram) : Bool :=
  r.blocks.all (fun b => b.term.exits.all (fiberOkB r b.region))

theorem fibersB_iff (r : RawProgram) : fibersB r = true ↔ FibersWFsyn r := by
  simp [fibersB, FibersWFsyn, fiberOkB_iff]

/-! ### clause 8 — `ResourcesWFsyn` -/

open Cas.Lang in
/-- An operand is INTERNAL to its block when it names a literal address or an
EARLIER answer of the same block. This is "resource tokens cannot escape their
scope" read at the estate's own straight-line carrier. -/
def PInInternal (i : Nat) : PIn → Prop
  | .lit _ => True
  | .ans j => j < i

open Cas.Lang in
def pInInternalB (i : Nat) : PIn → Bool
  | .lit _ => true
  | .ans j => decide (j < i)

open Cas.Lang in
theorem pInInternalB_iff (i : Nat) (v : PIn) : pInInternalB i v = true ↔ PInInternal i v := by
  cases v <;> simp [pInInternalB, PInInternal]

open Cas.Lang in
def LineInternal (i : Nat) : PLine → Prop
  | .put _ _ _ refs => ∀ x ∈ refs, PInInternal i x.2
  | .load s => PInInternal i s

open Cas.Lang in
def lineInternalB (i : Nat) : PLine → Bool
  | .put _ _ _ refs => refs.all (fun x => pInInternalB i x.2)
  | .load s => pInInternalB i s

open Cas.Lang in
theorem lineInternalB_iff (i : Nat) (l : PLine) : lineInternalB i l = true ↔ LineInternal i l := by
  cases l <;> simp [lineInternalB, LineInternal, pInInternalB_iff]

open Cas.Lang in
def BodyClosedFrom : Nat → PProg → Prop
  | _, [] => True
  | i, l :: ls => LineInternal i l ∧ BodyClosedFrom (i + 1) ls

open Cas.Lang in
def bodyClosedFromB : Nat → PProg → Bool
  | _, [] => true
  | i, l :: ls => lineInternalB i l && bodyClosedFromB (i + 1) ls

open Cas.Lang in
theorem bodyClosedFromB_iff (p : PProg) (i : Nat) :
    bodyClosedFromB i p = true ↔ BodyClosedFrom i p := by
  induction p generalizing i with
  | nil => simp [bodyClosedFromB, BodyClosedFrom]
  | cons l ls ih => simp [bodyClosedFromB, BodyClosedFrom, lineInternalB_iff, ih]

/-- A `scope` terminator's child block sits exactly one region DOWN. -/
def ScopeNested (r : RawProgram) (owner : Nat) : Term → Prop
  | .scope c _ => ∀ cb, r.blockOf c = some cb → ∀ d, r.regionOf cb.region = some d →
      d.parent = some owner
  | _ => True

def scopeNestedB (r : RawProgram) (owner : Nat) : Term → Bool
  | .scope c _ =>
      (match r.blockOf c with
       | none => true
       | some cb => match r.regionOf cb.region with
                    | none => true
                    | some d => decide (d.parent = some owner))
  | _ => true

theorem scopeNestedB_iff (r : RawProgram) (owner : Nat) (t : Term) :
    scopeNestedB r owner t = true ↔ ScopeNested r owner t := by
  cases t with
  | close ty => simp [scopeNestedB, ScopeNested]
  | perform o es => simp [scopeNestedB, ScopeNested]
  | foreign f es => simp [scopeNestedB, ScopeNested]
  | scope c es =>
      cases hc : r.blockOf c with
      | none => simp [scopeNestedB, ScopeNested, hc]
      | some cb =>
          cases hd : r.regionOf cb.region <;> simp [scopeNestedB, ScopeNested, hc, hd]

/-- Clause 8: block bodies are internally closed and scopes nest. -/
def ResourcesWFsyn (r : RawProgram) : Prop :=
  ∀ b ∈ r.blocks, BodyClosedFrom 0 b.body ∧ ScopeNested r b.region b.term

def resourcesB (r : RawProgram) : Bool :=
  r.blocks.all (fun b => bodyClosedFromB 0 b.body && scopeNestedB r b.region b.term)

theorem resourcesB_iff (r : RawProgram) : resourcesB r = true ↔ ResourcesWFsyn r := by
  simp [resourcesB, ResourcesWFsyn, bodyClosedFromB_iff, scopeNestedB_iff]

/-! ### clause 9 — `ForeignWF` -/

/-- Clause 9: a foreign call routes every failure its registry entry declares,
and has a normal edge. The registry is CLOSED — resolution itself is clause 1's
job, so this clause is about the entry's content being honoured. -/
def ForeignOk (r : RawProgram) : Term → Prop
  | .foreign f es => ∀ fd, r.foreignOf f = some fd →
      (∀ x ∈ fd.errs, ∃ e ∈ es, e.fail = some x) ∧ (∃ e ∈ es, e.fail = none)
  | _ => True

def foreignOkB (r : RawProgram) : Term → Bool
  | .foreign f es =>
      (match r.foreignOf f with
       | none => true
       | some fd => fd.errs.all (fun x => es.any (fun e => decide (e.fail = some x))) &&
                    es.any (fun e => decide (e.fail = none)))
  | _ => true

theorem foreignOkB_iff (r : RawProgram) (t : Term) : foreignOkB r t = true ↔ ForeignOk r t := by
  cases t with
  | close ty => simp [foreignOkB, ForeignOk]
  | perform o es => simp [foreignOkB, ForeignOk]
  | scope c es => simp [foreignOkB, ForeignOk]
  | foreign f es => cases hf : r.foreignOf f <;> simp [foreignOkB, ForeignOk, hf]

def ForeignWF (r : RawProgram) : Prop := ∀ b ∈ r.blocks, ForeignOk r b.term
def foreignB (r : RawProgram) : Bool := r.blocks.all (fun b => foreignOkB r b.term)

theorem foreignB_iff (r : RawProgram) : foreignB r = true ↔ ForeignWF r := by
  simp [foreignB, ForeignWF, foreignOkB_iff]

/-! ### clause 10 — `EntryWF` -/

def CloseOk (r : RawProgram) : Term → Prop
  | .close ty => ty = r.resultTy
  | _ => True

def closeOkB (r : RawProgram) : Term → Bool
  | .close ty => decide (ty = r.resultTy)
  | _ => true

theorem closeOkB_iff (r : RawProgram) (t : Term) : closeOkB r t = true ↔ CloseOk r t := by
  cases t <;> simp [closeOkB, CloseOk]

/-- Clause 10: the entry accepts exactly its declared input and every normal
return has the declared result type. -/
def EntryWF (r : RawProgram) : Prop :=
  (∃ b, r.blockOf r.entry = some b ∧ b.params = [r.entryTy]) ∧
  (∀ b ∈ r.blocks, CloseOk r b.term)

def entryB (r : RawProgram) : Bool :=
  (match r.blockOf r.entry with
   | none => false
   | some b => decide (b.params = [r.entryTy])) &&
  r.blocks.all (fun b => closeOkB r b.term)

theorem entryB_iff (r : RawProgram) : entryB r = true ↔ EntryWF r := by
  have h : (match r.blockOf r.entry with
            | none => false
            | some b => decide (b.params = [r.entryTy])) = true
      ↔ (∃ b, r.blockOf r.entry = some b ∧ b.params = [r.entryTy]) := by
    cases hb : r.blockOf r.entry <;> simp
  simp [entryB, EntryWF, h, closeOkB_iff]

/-! ### clause 11 — `AERWF` -/

/-- The synthesized error row: the ascending dedup of every alternative that
ESCAPES the graph. -/
def synthE (r : RawProgram) : List Nat :=
  ascend (concatMap (fun b => b.term.exits.filterMap Exit.escapes) r.blocks)

/-- The synthesized requirement row: what the performed operations and the
called foreign entries require. -/
def synthR (r : RawProgram) : List Nat :=
  ascend (concatMap (fun b =>
      (match b.term.performedOp with
       | none => []
       | some o => match r.opOf o with
                   | none => []
                   | some d => d.reqs) ++
      (match b.term with
       | .foreign f _ => match r.foreignOf f with
                         | none => []
                         | some fd => [fd.req]
       | _ => [])) r.blocks)

def synthAER (r : RawProgram) : AER := { A := r.resultTy, E := synthE r, R := synthR r }

/-- Clause 11: the synthesized `A/E/R` IS the declared triple. Note this is an
equation between two computed values, hence decidable on the nose; it is also
why `EC1-T016` (`∃! aer, SynthAER r aer`) is a tautology — see §10. -/
def AERWF (r : RawProgram) : Prop := synthAER r = r.declared
def aerB (r : RawProgram) : Bool := decide (synthAER r = r.declared)

theorem aerB_iff (r : RawProgram) : aerB r = true ↔ AERWF r := by simp [aerB, AERWF]

/-! ### clause 12 — `PresentationWFsyn` -/

/-- The normalizer. Keep-LAST dedup on every keyed table. It does not touch the
handler table, which clause 5 counts. -/
def normalizeRaw (r : RawProgram) : RawProgram :=
  { r with blocks := dedupLastBy (·.id) r.blocks,
           ops := dedupLastBy (·.op) r.ops,
           foreigns := dedupLastBy (·.fid) r.foreigns,
           regions := dedupLastBy (·.rid) r.regions }

/-- Clause 12: normalization does not change what a reference RESOLVES TO.
Reference-target equality after `normalizeRaw`, computed by recompute-and-
compare over the finite id set. Never `SemEq`, never a denotation: `R4` rules
that identity hashes presentations, so a well-formedness clause whose criterion
is meaning is out of bounds before it is undecidable. -/
def PresentationWFsyn (r : RawProgram) : Prop :=
  ∀ b ∈ r.blocks, (normalizeRaw r).blockOf b.id = r.blockOf b.id

def presentationB (r : RawProgram) : Bool :=
  r.blocks.all (fun b => decide ((normalizeRaw r).blockOf b.id = r.blockOf b.id))

theorem presentationB_iff (r : RawProgram) : presentationB r = true ↔ PresentationWFsyn r := by
  simp [presentationB, PresentationWFsyn]


/-! ## §4 — `ProgramWF`, and the first-error checker that decides it

`ProgramWF` is the twelve-way conjunction of the clause layer above. The
checker is a SEPARATE object: a structural recursion over a frozen clause
table, whose entries are the twelve `Bool`s. It does not mention `ProgramWF`,
and nothing in its definition could be replaced by `decide (ProgramWF r)`
without changing what the row proves — see §6. -/

/-- Twelve clauses. Semantic words pinned syntactically: `RowsWFsyn` reads the
failure alternatives a block's exit edges name; `RegionsWFsyn`/`FibersWFsyn`/
`ResourcesWFsyn` are syntactic containment in the region index order;
`HandlersWFsyn` quantifies over DECLARED blocks; `PresentationWFsyn` is
reference-target equality after `normalizeRaw`, never `SemEq`. -/
def ProgramWF (r : RawProgram) : Prop :=
  IdsWF r ∧ TypesWF r ∧ RowsWFsyn r ∧ RegionsWFsyn r ∧ HandlersWFsyn r ∧
  ResumeWF r ∧ FibersWFsyn r ∧ ResourcesWFsyn r ∧ ForeignWF r ∧ EntryWF r ∧
  AERWF r ∧ PresentationWFsyn r

/-- Clause names. -/
inductive Clause where
  | ids | types | rows | regions | handlers | resume
  | fibers | resources | foreign | entry | aer | presentation
  deriving DecidableEq

/-- A SINGLE first-error value (`R16` part 1, `EC1-CE031`), never a list and
never a `NonEmpty`. The offending row and the expected/actual types are
`EC1-T015`'s business and are deliberately absent here. -/
structure Diagnostic where
  clause : Clause
  deriving DecidableEq

/-- The frozen clause order. This is the object `EC1-T015` calls the "canonical
checker order"; making it a DECLARED table rather than an emergent property of
`check`'s recursion is what keeps that row from collapsing to `id`. -/
def clauseTable : List (Clause × (RawProgram → Bool)) :=
  [(.ids, idsB), (.types, typesB), (.rows, rowsB), (.regions, regionsB),
   (.handlers, handlersB), (.resume, resumeB), (.fibers, fibersB),
   (.resources, resourcesB), (.foreign, foreignB), (.entry, entryB),
   (.aer, aerB), (.presentation, presentationB)]

/-- Fail-fast: scan the frozen table, stop at the first clause that says no. -/
def runClauses (r : RawProgram) : List (Clause × (RawProgram → Bool)) → Except Diagnostic Unit
  | [] => .ok ()
  | (c, f) :: rest => if f r then runClauses r rest else .error ⟨c⟩

/-- The decision layer. Total, structural, and defined WITHOUT reference to
`ProgramWF`. -/
def checkClauses (r : RawProgram) : Except Diagnostic Unit := runClauses r clauseTable

/-- The estate ships this shape at ONE clause: `Cas/Core/Admission.lean:49`
`checkRefs` (a fail-fast scan returning a single error) with `:60`
`checkRefs_ok_iff` (soundness AND completeness in one iff). `EC1-T010` and
`EC1-T011` are that iff's two directions there; the separation earns its keep
only at two or more clauses, which is what the table below supplies. -/
theorem runClauses_ok_iff (r : RawProgram) (t : List (Clause × (RawProgram → Bool))) :
    runClauses r t = .ok () ↔ ∀ cf ∈ t, cf.2 r = true := by
  induction t with
  | nil => simp [runClauses]
  | cons cf rest ih =>
    obtain ⟨c, f⟩ := cf
    by_cases hf : f r = true
    · simp [runClauses, hf, ih]
    · simp [runClauses, hf]

/-- First-error SOUNDNESS at the composition (`R16` part 1): the clause the
checker names is one the input actually fails, and the clauses before it in the
frozen order all hold. -/
theorem runClauses_error_condemns {r : RawProgram} {t : List (Clause × (RawProgram → Bool))}
    {d : Diagnostic} (h : runClauses r t = .error d) :
    ∃ pre f post, t = pre ++ (d.clause, f) :: post ∧
      (∀ cf ∈ pre, cf.2 r = true) ∧ f r = false := by
  induction t with
  | nil => simp [runClauses] at h
  | cons cf rest ih =>
    obtain ⟨c, f⟩ := cf
    by_cases hf : f r = true
    · rw [runClauses, if_pos hf] at h
      obtain ⟨pre, g, post, ht, hpre, hg⟩ := ih h
      refine ⟨(c, f) :: pre, g, post, by simp [ht], ?_, hg⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hf
      · exact hpre x hx
    · rw [runClauses, if_neg hf] at h
      cases h
      exact ⟨[], f, rest, by simp, by simp, Bool.not_eq_true _ |>.mp hf⟩

/-- **The row's content.** Twelve independently defined `Bool` decisions,
reflected one clause at a time, composed by first-error `Except` sequencing.
This is `PROOF-DAG.md` §16's Checker route, and it is where every part of
`EC1-T010` that is not bookkeeping lives. -/
theorem clauses_sound {r : RawProgram} (h : checkClauses r = .ok ()) : ProgramWF r := by
  have h' := (runClauses_ok_iff r clauseTable).mp h
  exact ⟨(idsB_iff r).mp (h' (.ids, idsB) (by simp [clauseTable])),
         (typesB_iff r).mp (h' (.types, typesB) (by simp [clauseTable])),
         (rowsB_iff r).mp (h' (.rows, rowsB) (by simp [clauseTable])),
         (regionsB_iff r).mp (h' (.regions, regionsB) (by simp [clauseTable])),
         (handlersB_iff r).mp (h' (.handlers, handlersB) (by simp [clauseTable])),
         (resumeB_iff r).mp (h' (.resume, resumeB) (by simp [clauseTable])),
         (fibersB_iff r).mp (h' (.fibers, fibersB) (by simp [clauseTable])),
         (resourcesB_iff r).mp (h' (.resources, resourcesB) (by simp [clauseTable])),
         (foreignB_iff r).mp (h' (.foreign, foreignB) (by simp [clauseTable])),
         (entryB_iff r).mp (h' (.entry, entryB) (by simp [clauseTable])),
         (aerB_iff r).mp (h' (.aer, aerB) (by simp [clauseTable])),
         (presentationB_iff r).mp (h' (.presentation, presentationB) (by simp [clauseTable]))⟩

/-- The converse. Owed with the row: it is what makes `checkClauses` a DECISION
procedure rather than a filter, and it is exactly `EC1-T011`'s content at this
carrier. Soundness composes over first-error sequencing for free; completeness
does not — it needs every clause decided against the SAME raw value, which §7
shows is the whole order obligation. -/
theorem clauses_complete {r : RawProgram} (h : ProgramWF r) : checkClauses r = .ok () := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  refine (runClauses_ok_iff r clauseTable).mpr ?_
  intro cf hcf
  simp only [clauseTable, List.mem_cons, List.not_mem_nil, or_false] at hcf
  rcases hcf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact (idsB_iff r).mpr h1
  · exact (typesB_iff r).mpr h2
  · exact (rowsB_iff r).mpr h3
  · exact (regionsB_iff r).mpr h4
  · exact (handlersB_iff r).mpr h5
  · exact (resumeB_iff r).mpr h6
  · exact (fibersB_iff r).mpr h7
  · exact (resourcesB_iff r).mpr h8
  · exact (foreignB_iff r).mpr h9
  · exact (entryB_iff r).mpr h10
  · exact (aerB_iff r).mpr h11
  · exact (presentationB_iff r).mpr h12

/-- The two directions together: the checker DECIDES `ProgramWF`. -/
theorem checkClauses_ok_iff (r : RawProgram) : checkClauses r = .ok () ↔ ProgramWF r :=
  ⟨clauses_sound, clauses_complete⟩

set_option warn.classDefReducibility false in
/-- And therefore `ProgramWF` is decidable — CONSTRUCTIVELY, from the checker,
with no classical input. The DAG lists decidability as a DEPENDENCY of
`EC1-T011/T012`; it is a consequence. Deliberately a `def`, not an `instance`:
instance resolution must never silently route a `ProgramWF` goal through a
whole-program check (the discipline of `Cas/IR/Reach.lean:550`
`decidableReach`, which carries no `instance` attribute for the same reason). -/
def decidableProgramWF : DecidablePred ProgramWF := fun r =>
  match h : checkClauses r with
  | .ok () => isTrue (clauses_sound h)
  | .error _ => isFalse (fun hwf => by rw [clauses_complete hwf] at h; simp at h)

/-! ## §5 — the checked carrier, `check`, and `EC1-T010`

Normalization sits INSIDE the payload, strictly AFTER the decision. That order
is not a style preference: §7 proves a checker that normalizes first cannot
prove this row. -/

/-- The checked payload.

NOTE WHAT IS NOT A FIELD: `wf : ProgramWF raw`. `ALGEBRA.md:319-320` specifies
that `CheckedProgram` "stores an erased raw value, normalized lookup tables,
and evidence of `ProgramWF`". §6 proves that storing the evidence discharges
`EC1-T010` with NO CHECKER AT ALL. So the evidence lives in the theorem here,
not in the structure. That is a deliberate divergence and it is what makes the
row carry content. -/
structure CheckedProgram (aer : AER) where
  raw    : RawProgram
  norm   : RawProgram
  normEq : norm = normalizeRaw raw
  aerEq  : synthAER raw = aer

/-- `EC1-D024`. First the decision, on the RAW input; then the payload, which
is where normalization happens. -/
def check (r : RawProgram) : Except Diagnostic (Sigma CheckedProgram) :=
  match checkClauses r with
  | .error d => .error d
  | .ok () =>
      .ok ⟨synthAER r, { raw := r, norm := normalizeRaw r, normEq := rfl, aerEq := rfl }⟩

/-- An accepted input passed every clause. This is the only bridge from `check`
to the clause layer, and it is why `check_sound` has to go through
`clauses_sound`: there is no `wf` field to project. -/
theorem check_ok_clauses {r : RawProgram} {x : Sigma CheckedProgram} (h : check r = .ok x) :
    checkClauses r = .ok () := by
  unfold check at h
  split at h
  · exact absurd h (by simp)
  · next hc => exact hc

/-- **`EC1-T010`.** `check r = ok ⟨a, p⟩ → ProgramWF r`, at this carrier. -/
theorem check_sound {r : RawProgram} {aer : AER} {p : CheckedProgram aer}
    (h : check r = .ok ⟨aer, p⟩) : ProgramWF r :=
  clauses_sound (check_ok_clauses h)

/-- `EC1-T011` at this carrier, with the alphabet BOUND. The DAG writes
`ProgramWF r -> exists p, check r = ok <a,p>` with `a` free; under universal
closure that claims a well-formed program checks at every `AER`, which is false
as soon as `AER` has two inhabitants. -/
theorem check_complete {r : RawProgram} (h : ProgramWF r) :
    ∃ (aer : AER) (p : CheckedProgram aer), check r = .ok ⟨aer, p⟩ := by
  refine ⟨synthAER r, { raw := r, norm := normalizeRaw r, normEq := rfl, aerEq := rfl }, ?_⟩
  unfold check
  rw [clauses_complete h]

/-- `EC1-T012` at this carrier, derived from `EC1-T010` and `EC1-T011` with NO
decidability premise. `PROOF-DAG.md:214` lists `decidable WF` as a dependency of
`T012`; `Except`'s two arms already supply everything. -/
theorem check_error_iff (r : RawProgram) :
    (∃ d, check r = .error d) ↔ ¬ ProgramWF r := by
  constructor
  · rintro ⟨d, hd⟩ hwf
    obtain ⟨aer, p, hp⟩ := check_complete hwf
    rw [hd] at hp
    simp at hp
  · intro hn
    cases h : check r with
    | ok x => exact absurd (clauses_sound (check_ok_clauses h)) hn
    | error d => exact ⟨d, rfl⟩


/-! ## §6 — the vacuity guard: why `CheckedProgram` must NOT store the evidence

`ALGEBRA.md:319-320` specifies that `CheckedProgram` "stores an erased raw
value, normalized lookup tables, and evidence of `ProgramWF`". Under that
carrier `EC1-T010` is discharged by the STRUCTURE, not by the checker: the
guard below proves the row's exact shape for an ARBITRARY `chk`, consuming
nothing about it beyond the fact that its accepted payload carries the input
back. A
checker that skipped every clause would satisfy it.

That is the same defect family the DAG already deleted rows for (`EC1-T003`,
`T035`, `T115`) and is one level sharper than "trivially true": the statement
is not provable of every program (an unsatisfiable `ProgramWF` leaves
`CheckedWithEvidence` uninhabited), it is INFORMATION-FREE about the checker.

Hence §5's carrier omits the field. -/

/-- The carrier `ALGEBRA.md:319-320` specifies. -/
structure CheckedWithEvidence (aer : AER) where
  raw : RawProgram
  wf  : ProgramWF raw

/-- **The guard.** `EC1-T010`'s exact shape, for ANY `chk` whose accepted
payload carries its input back. No soundness lemma, no clause, no `check`. -/
theorem evidence_carrier_makes_T010_a_projection
    (chk : RawProgram → Except Diagnostic (Sigma CheckedWithEvidence))
    (hraw : ∀ r aer p, chk r = .ok ⟨aer, p⟩ → p.raw = r)
    {r : RawProgram} {aer : AER} {p : CheckedWithEvidence aer}
    (h : chk r = .ok ⟨aer, p⟩) : ProgramWF r := by
  rw [← hraw r aer p h]
  exact p.wf

/-- And the proof term is literally the field selector. -/
theorem evidence_is_the_field {aer : AER} (p : CheckedWithEvidence aer) :
    ProgramWF p.raw := p.wf

theorem evidence_is_the_field_is_the_projection {aer : AER} (p : CheckedWithEvidence aer) :
    evidence_is_the_field p = p.wf := rfl

/-! ## §7 — the order obligation

`EC1-T010`'s conclusion is about the RAW input; `EC1-K10`
(`CONTRACT-PACKET.md:306-310`) separately requires
`erase checked = normalizeRaw (erase checked)`. Read together they invite a
checker that normalizes first and decides the normal form. That checker cannot
prove this row, and the reason is not delicate: normalization does not PRESERVE
clause 1, it CREATES it (`dedupLast_keys_distinct`, §1).

This is `EC1-CE030`/`R16` part 2 landing one row earlier than the register
files it. Proved here at THIS file's own normalizer and its own twelve-clause
`ProgramWF`, so no `Classical.choice` is inherited from `List.mergeSort`. -/

open Cas.Lang in
private def b0 : Block :=
  { id := 0, params := [0], region := 0, body := ([] : PProg), term := .close 7 }

private def rd0 : RegionDecl := { rid := 0, parent := none }

/-- A one-block program that passes every clause. -/
def wNorm : RawProgram :=
  { blocks := [b0], ops := [], foreigns := [], handlers := [], regions := [rd0],
    entry := 0, entryTy := 0, resultTy := 7, declared := { A := 7, E := [], R := [] } }

/-- The same program with its block table duplicated: clause 1 fails. -/
def wRaw : RawProgram := { wNorm with blocks := [b0, b0] }

theorem wNorm_admits : checkClauses wNorm = .ok () := by rfl

theorem wRaw_rejected : checkClauses wRaw = .error ⟨Clause.ids⟩ := by rfl

theorem normalize_wRaw : normalizeRaw wRaw = wNorm := by rfl

theorem wNorm_wf : ProgramWF wNorm := clauses_sound wNorm_admits

theorem wRaw_not_wf : ¬ ProgramWF wRaw := by
  intro h
  have hc := clauses_complete h
  rw [wRaw_rejected] at hc
  simp at hc

/-- **The order obligation.** There is a raw program whose NORMAL FORM is
well-formed while it is not. A checker that normalizes before it decides
therefore proves nothing about `r`, which is exactly what `EC1-T010`'s
conclusion is about. -/
theorem normalize_then_check_cannot_prove_T010 :
    ∃ r : RawProgram, ProgramWF (normalizeRaw r) ∧ ¬ ProgramWF r :=
  ⟨wRaw, by rw [normalize_wRaw]; exact wNorm_wf, wRaw_not_wf⟩

/-- Stated as the refuted implication, which is the form a normalize-first
checker would need. -/
theorem programWF_normalizeRaw_forward_is_false :
    ¬ ∀ r : RawProgram, ProgramWF (normalizeRaw r) → ProgramWF r := by
  intro hall
  obtain ⟨r, hn, hr⟩ := normalize_then_check_cannot_prove_T010
  exact hr (hall r hn)

/-- The positive boundary, so this is not read as an attack on normalization:
where clause 1 already holds, keep-last dedup is the IDENTITY. -/
theorem dedupLastBy_id_of_distinct {α : Type} (key : α → Nat) (xs : List α)
    (h : Distinct (xs.map key)) : dedupLastBy key xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨hx, hrest⟩ := h
    have hmb : memB (key x) (xs.map key) = false := (memB_eq_false_iff _ _).mpr hx
    rw [dedupLastBy, if_neg (by simp [hmb]), ih hrest]

theorem normalizeRaw_id_of_ids {r : RawProgram} (h : IdsWF r) : normalizeRaw r = r := by
  obtain ⟨h1, h2, h3, _, h5, _⟩ := h
  simp [normalizeRaw, dedupLastBy_id_of_distinct _ _ h1, dedupLastBy_id_of_distinct _ _ h2,
        dedupLastBy_id_of_distinct _ _ h3, dedupLastBy_id_of_distinct _ _ h5]

/-- Non-vacuity, both ways: `check` accepts something and rejects something.
NOT completeness — `PROOF-DAG.md` §16 prohibits "using successful examples as
completeness", and `clauses_complete`/`check_complete` above are the real
thing. These two rule out only the degenerate readings in which `check` never
accepts (so `check_sound` is empty) or never rejects (so `ProgramWF` is a
no-op). -/
theorem check_accepts : ∃ (aer : AER) (p : CheckedProgram aer), check wNorm = .ok ⟨aer, p⟩ :=
  check_complete wNorm_wf

theorem check_rejects : check wRaw = .error ⟨Clause.ids⟩ := by rfl

/-! ### A non-degenerate admitted program

`wNorm` is one block and no edges, so on its own it leaves open that the twelve
clauses are only JOINTLY satisfiable on degenerate input — which would make
`clauses_complete` cheap. `wRich` closes that: four blocks, a `scope` into a
nested region, a `perform` with a direct handler, a `foreign` call against the
closed registry, a `close` at the declared result type, a CYCLE back to an
earlier block (`ALGEBRA.md`'s "Cycles are ordinary references to earlier
blocks"), two ESCAPING typed failures that the declared `E` has to carry, and a
non-empty `PProg` body whose second line reads the first line's answer. -/

open Cas in
private def addr1 : Addr32 := ⟨List.replicate 32 1, by simp⟩

open Cas.Lang in
private def rb0 : Block :=
  { id := 0, params := [0], region := 0, body := ([] : PProg),
    term := .scope 2 [{ label := 0, fail := none, dest := some 1, carry := [] }] }

open Cas.Lang in
private def rb1 : Block :=
  { id := 1, params := [], region := 0, body := ([] : PProg),
    term := .perform 5 [{ label := 0, fail := none, dest := some 3, carry := [] },
                        { label := 1, fail := some 9, dest := none, carry := [] }] }

open Cas.Lang in
private def rb2 : Block :=
  { id := 2, params := [], region := 1, body := ([] : PProg),
    term := .foreign 7 [{ label := 0, fail := none, dest := some 0, carry := [0] },
                        { label := 1, fail := some 3, dest := none, carry := [] }] }

open Cas.Lang in
private def rb3 : Block :=
  { id := 3, params := [], region := 0,
    body := ([PLine.load (PIn.lit addr1), PLine.load (PIn.ans 0)] : PProg),
    term := .close 7 }

def wRich : RawProgram :=
  { blocks := [rb0, rb1, rb2, rb3],
    ops := [{ op := 5, errs := [9], reqs := [4] }],
    foreigns := [{ fid := 7, req := 2, errs := [3] }],
    handlers := [{ op := 5, blk := 0 }],
    regions := [{ rid := 0, parent := none }, { rid := 1, parent := some 0 }],
    entry := 0, entryTy := 0, resultTy := 7,
    declared := { A := 7, E := [3, 9], R := [2, 4] } }

theorem wRich_admits : checkClauses wRich = .ok () := by rfl

theorem wRich_wf : ProgramWF wRich := clauses_sound wRich_admits

theorem check_accepts_a_nondegenerate_program :
    ∃ (aer : AER) (p : CheckedProgram aer), check wRich = .ok ⟨aer, p⟩ :=
  check_complete wRich_wf

/-- And its synthesized triple IS the declared one, so clause 11 is doing work
on this witness rather than being satisfied by an empty row. -/
theorem wRich_aer : synthAER wRich = { A := 7, E := [3, 9], R := [2, 4] } := by rfl

/-! ## §8 — the twelve clauses are NOT independent

Two entailments, both cheap, both worth the coordinator's attention because the
packet presents `ALGEBRA.md:295-317` as twelve separate obligations. -/

/-- Clause 12 is DERIVABLE from clause 1. Under any lookup-based reference
resolver, "normalization does not change reference meaning" is a consequence of
"every table is duplicate-free", because normalization is then the identity.
`PresentationWFsyn` earns its keep only as documentation of what clause 12 may
NOT mean. -/
theorem presentation_follows_from_ids {r : RawProgram} (h : IdsWF r) :
    PresentationWFsyn r := by
  intro b _
  rw [normalizeRaw_id_of_ids h]

/-- `EC1-T016`'s replacement, as the T010 scout recommended: pin the
SYNTHESIZER by its law rather than a value in its graph. At this carrier it is
a projection of clause 11 — which is the point: `AERWF` being decidable is what
makes the agreement content, and `EC1-T016` adds nothing to it. -/
theorem aer_synthesis_agrees {r : RawProgram} (h : ProgramWF r) :
    synthAER r = r.declared := h.2.2.2.2.2.2.2.2.2.2.1

/-- And `EC1-T016` as written is vacuous here: `∃!` over a function's graph,
provable with the `ProgramWF` premise DELETED. (`∃!` is Mathlib notation and
`library/cas` carries no Mathlib, so it is spelled out.) -/
theorem synthAER_uniqueness_needs_no_premise (r : RawProgram) :
    ∃ a : AER, synthAER r = a ∧ ∀ a', synthAER r = a' → a' = a :=
  ⟨synthAER r, rfl, fun _ h => h.symm⟩

/-! ### Clause 5's reading is strictly stronger than graph reachability

`HandlersWFsyn` quantifies over DECLARED blocks. The witness below has an entry
with NO outgoing edge — so nothing but the entry is graph-reachable — and a
second block performing an unhandled operation. It is REJECTED, at clause 5.

That is sound and conservative for `EC1-T010`, and because the strengthening is
written into `ProgramWF` itself rather than only into `check`, `EC1-T011`
survives it (`clauses_complete` above is proved against the same predicate).
Approximating in `check` alone would keep `T010` and kill `T011`. -/

open Cas.Lang in
private def b1 : Block :=
  { id := 1, params := [], region := 0, body := ([] : PProg),
    term := .perform 1 [{ label := 0, fail := none, dest := some 1, carry := [] }] }

def wUnreach : RawProgram :=
  { wNorm with blocks := [b0, b1], ops := [{ op := 1, errs := [], reqs := [] }] }

/-- The entry names no successor, yet the program is condemned at clause 5. -/
theorem declared_reading_is_strictly_stronger :
    (∀ b ∈ wUnreach.blocks, b.id = wUnreach.entry → b.term.exits = []) ∧
      checkClauses wUnreach = .error ⟨Clause.handlers⟩ := by
  refine ⟨?_, by rfl⟩
  decide


/-! ## §A — BREAKER ATTACK SECTION (not part of the reviewed file)

Everything from here down was written by the EC1-S2 breaker for `EC1-T010`.
Lines 1-1185 above are byte-identical to
`.staging/effect-core-v1/workshop/s2/T010.lean` lines 1-1185, so every witness
below is about the REVIEWED definitions and not a re-statement of them. Verify
with:

```
diff <(sed -n '1,1185p' .staging/effect-core-v1/workshop/s2/T010.lean) \
     <(sed -n '1,1185p' .staging/effect-core-v1/workshop/s2/attack-EC1-T010.lean)
```

The row `check_sound` itself is NOT refuted: §A1-§A5 are attacks on the MODEL,
not on the proof. Each names the falsifier it runs.
-/

/-! ### §A1 — `EC1-F01` family: a DANGLING REGION PARENT is admitted

`IdsWF`'s own docstring (line 355 above, and `ALGEBRA.md:298`) reads "every
table is duplicate-free and **every reference resolves**". `IdsWF` resolves
block ids, op ids, foreign ids and each block's own region — but NOT a region's
`parent` link. `RegionAcyclic` only demands `p < rid`, which is a numeric
comparison, not a resolution. So a region may name a parent that does not
exist, in an ACCEPTED program. -/

open Cas.Lang in
private def bDangle : Block :=
  { id := 0, params := [0], region := 3, body := ([] : PProg), term := .close 7 }

def wDangleParent : RawProgram :=
  { wNorm with blocks := [bDangle], regions := [{ rid := 3, parent := some 1 }] }

theorem dangling_region_parent_is_admitted :
    checkClauses wDangleParent = .ok ()
  ∧ ProgramWF wDangleParent
  ∧ wDangleParent.regions = [{ rid := 3, parent := some 1 }]
  ∧ wDangleParent.regionOf 1 = none := by
  refine ⟨by rfl, clauses_sound (by rfl), by rfl, by rfl⟩

/-! ### §A2 — `EC1-F08`: the FOREIGN REGISTRY is a field of the program

`R7` rules that programs are content and hosts are code. `ALGEBRA.md:312` reads
"every foreign ID resolves to a registry entry". Here the registry IS
`r.foreigns`, a field of `RawProgram`, so the raw content decides which host
callbacks exist. A program may call any `fid` at all and supply the row that
makes the call resolve; deleting that row is what turns admission around, not
anything the host says. -/

open Cas.Lang in
private def fb0 : Block :=
  { id := 0, params := [0], region := 0, body := ([] : PProg),
    term := .foreign 999 [{ label := 0, fail := none, dest := some 1, carry := [] },
                          { label := 1, fail := some 3, dest := none, carry := [] }] }

open Cas.Lang in
private def fb1 : Block :=
  { id := 1, params := [], region := 0, body := ([] : PProg), term := .close 7 }

/-- Calls host callback `999`, and registers `999` itself. -/
def wSelfRegistered : RawProgram :=
  { blocks := [fb0, fb1], ops := [], foreigns := [{ fid := 999, req := 2, errs := [3] }],
    handlers := [], regions := [{ rid := 0, parent := none }],
    entry := 0, entryTy := 0, resultTy := 7,
    declared := { A := 7, E := [3], R := [2] } }

theorem foreign_registry_is_program_supplied :
    checkClauses wSelfRegistered = .ok ()
  ∧ ProgramWF wSelfRegistered
  ∧ (∃ es, fb0.term = Term.foreign 999 es)
  ∧ checkClauses { wSelfRegistered with foreigns := [] } = .error ⟨Clause.ids⟩ := by
  refine ⟨by rfl, clauses_sound (by rfl), ⟨_, rfl⟩, by rfl⟩

/-- Sharper: the registry row is the ONLY thing that changed, so admission of a
host call is decided by the content, not by the host. -/
theorem host_closure_is_decided_by_content :
    ({ wSelfRegistered with foreigns := [] } : RawProgram).blocks = wSelfRegistered.blocks
  ∧ checkClauses wSelfRegistered = .ok ()
  ∧ ¬ ProgramWF { wSelfRegistered with foreigns := [] } := by
  refine ⟨rfl, by rfl, fun h => ?_⟩
  have hc := clauses_complete h
  rw [show checkClauses { wSelfRegistered with foreigns := [] } = .error ⟨Clause.ids⟩ from by rfl] at hc
  simp at hc

/-! ### §A3 — `EC1-F07`: one resume token, two syntactic owners, ADMITTED

`ALGEBRA.md:306-307` reads "every one-shot resume token has one syntactic owner
**and** no duplicate consumption path within a single transition". `ResumeWF`
above keeps only the second half: it is `Distinct` per block. The file's own
non-degeneracy witness `wRich` reuses label `0` in three different blocks and
is accepted, so the "one syntactic owner" half of clause 6 is not modelled at
all. `EC1-F07` runs GREEN against this checker. -/

theorem one_resume_token_three_owners :
    checkClauses wRich = .ok ()
  ∧ rb0.term.exits.map (·.label) = [0]
  ∧ rb1.term.exits.map (·.label) = [0, 1]
  ∧ rb2.term.exits.map (·.label) = [0, 1]
  ∧ rb0.id ≠ rb1.id ∧ rb1.id ≠ rb2.id := by
  refine ⟨by rfl, by rfl, by rfl, by rfl, by decide, by decide⟩

/-! ### §A4 — `EC1-F81` stays RED (this one is a PASS)

Two independent defects in one raw program: a duplicated block table (clause 1)
and an entry whose parameters do not match `entryTy` (clause 10). The checker
names ONLY the earlier clause. That is `R16` part 1 exactly, and it is what
`EC1-F81` demands stay impossible: no accumulating reading is available here. -/

def wTwoDefects : RawProgram := { wRaw with entryTy := 4 }

theorem F81_later_diagnostic_is_unavailable :
    idsB wTwoDefects = false
  ∧ entryB wTwoDefects = false
  ∧ checkClauses wTwoDefects = .error ⟨Clause.ids⟩
  ∧ checkClauses wTwoDefects ≠ .error ⟨Clause.entry⟩ := by
  refine ⟨by rfl, by rfl, by rfl, ?_⟩
  intro hcon
  rw [show checkClauses wTwoDefects = Except.error ⟨Clause.ids⟩ from rfl] at hcon
  simp at hcon

/-! ### §A5 — clause 3's escape half is ENTAILED by clause 11

§8 above reports ONE non-independence (clause 12 from clause 1). There is a
second one it does not report: `AERWF` fixes `declared.E` to `synthE`, which is
`ascend` of every escaped alternative, so the escaped-failure half of
`RowsWFsyn` is a consequence. The twelve clauses are less independent than §8
already says. -/

theorem mem_insAsc (x y : Nat) (l : List Nat) : y ∈ insAsc x l ↔ (y = x ∨ y ∈ l) := by
  induction l with
  | nil => simp [insAsc]
  | cons z t ih =>
    rw [insAsc]
    split
    · simp
    · split
      · next hne =>
          subst hne
          simp only [List.mem_cons]
          constructor
          · intro h
            rcases h with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
          · intro h
            rcases h with h | h | h
            · exact Or.inl h
            · exact Or.inl h
            · exact Or.inr h
      · simp only [List.mem_cons, ih]
        constructor
        · intro h
          rcases h with h | h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · intro h
          rcases h with h | h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)

theorem mem_ascend (y : Nat) (l : List Nat) : y ∈ ascend l ↔ y ∈ l := by
  induction l with
  | nil => simp [ascend]
  | cons x t ih => rw [ascend, mem_insAsc]; simp [ih]

theorem mem_concatMap {α : Type} (f : α → List Nat) (xs : List α) {y : Nat} {a : α}
    (ha : a ∈ xs) (hy : y ∈ f a) : y ∈ concatMap f xs := by
  induction xs with
  | nil => simp at ha
  | cons c cs ih =>
    rw [concatMap, List.mem_append]
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact Or.inl hy
    · exact Or.inr (ih ha')

/-- Clause 11 already forces the escape half of clause 3. -/
theorem rows_escape_half_follows_from_aer {r : RawProgram} (h : AERWF r) :
    ∀ b ∈ r.blocks, ∀ e ∈ b.term.exits, OptAll e.escapes (fun x => x ∈ r.declared.E) := by
  intro b hb e he x hx
  have hE : r.declared.E = synthE r := by rw [← h]; rfl
  rw [hE, synthE, mem_ascend]
  exact mem_concatMap _ _ hb (List.mem_filterMap.mpr ⟨e, he, hx⟩)

/-! ### §A6 — clause 5 drops `ALGEBRA.md`'s parent-delegation alternative

`ALGEBRA.md:304-305` reads "exactly one typed clause for every reachable
operation **or a named parent delegation**". The carrier has no delegation
construct — `HandlerClause` is `(op, blk)` and `RawProgram` has no delegation
table — so the disjunct is not narrowed, it is absent. `HandlersWFsyn` demands
the direct clause unconditionally, which REJECTS every program `ALGEBRA.md`
would admit by delegation. That is a second, undeclared strengthening of clause
5 on top of the declared-vs-reachable one, and it is the one that would kill
`EC1-T011` at a carrier that has delegation. The witness is the absence itself:
`HandlerClause` has exactly two fields. -/

theorem handler_clause_has_no_delegation_alternative
    (h : HandlerClause) : h = { op := h.op, blk := h.blk } := rfl

end EffectCoreT010

/-! ## §A7 — receipts for the attack section

No `sorry`, no `axiom`, no `native_decide`, no `#eval` carrying a claim.
Every witness below is about the definitions in lines 1-1185, which are
byte-identical to the reviewed `T010.lean`. -/

#print axioms EffectCoreT010.dangling_region_parent_is_admitted
#print axioms EffectCoreT010.foreign_registry_is_program_supplied
#print axioms EffectCoreT010.host_closure_is_decided_by_content
#print axioms EffectCoreT010.one_resume_token_three_owners
#print axioms EffectCoreT010.F81_later_diagnostic_is_unavailable
#print axioms EffectCoreT010.mem_insAsc
#print axioms EffectCoreT010.mem_ascend
#print axioms EffectCoreT010.mem_concatMap
#print axioms EffectCoreT010.rows_escape_half_follows_from_aer
#print axioms EffectCoreT010.handler_clause_has_no_delegation_alternative
