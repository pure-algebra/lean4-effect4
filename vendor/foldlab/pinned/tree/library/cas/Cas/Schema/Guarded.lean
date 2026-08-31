import Cas.Schema.SelfCodec

/-!
# Guardedness — the references table's one discipline

A revision-1 document is a references TABLE (names to codes) and a root
code. The table is where recursion lives: a code reaches another entry
through `Ast.reference`, and `Ast.susp` is the guard that makes the
reaching productive.

The discipline this module decides is the one the ruling names:

> every cycle passes through a `susp`

stated, as the plan itself states it, as acyclicity of the NON-SUSPEND
edge relation. `Ast.bareRefs` is that relation's generator: it collects
the names a code mentions at positions no `susp` guards, stopping dead
at every `.susp`. So a cycle that passes through a guard contributes no
edge at all, and a cycle that does not is exactly a cycle of `bareRefs`.

Why the discipline is needed: a cycle with no guard on it cannot be
BUILT. Revival walks the code eagerly, so unfolding `A` to get `A`
again yields no node — and Effect's own codec does not refuse one.
`{"A":{"$ref":"B"},"B":{"$ref":"A"}}` reads back cleanly through
`SchemaRepresentation.fromJson`, which the spelling probe pins
(`library/effects/test/SchemaReferencesPin.test.ts`). The refusal is
this door's to make or nobody's.

## What this does NOT decide (break pass 2026-08-30, finding F2)

CONSTRUCTIBILITY, not PRODUCTIVITY. `Ast.susp` is a DELAY, not a
constructor: putting the recursive occurrence under one defers the
loop, it does not break it. So a document can pass this door and still
have no value at the end of it. Three witnesses, all `Guarded` and all
admitted by both doors:

- `{"A": susp (reference "A")}` — Effect's validator runs forever;
- `{"A": susp (union [reference "A", null])}` — it overflows the stack;
- `{"A": susp (reference "B"), "B": reference "A"}` — the same knot at
  one remove, and the cycle really does pass through a `susp`.

The control is `guardedList` below, which decodes in a millisecond on
the same path — so the discipline is right about the shape Effect
emits, and it is not a termination claim about forcing the result.
Deciding productivity needs a second relation over HEAD positions —
what a name reaches through `susp` wrappers alone, before any
constructor builds anything — and `union` builds nothing either, so it
is a ruling and not a line. It is owed, not claimed. The witnesses are
`contracts/attacks/PDD-3/Attack.lean` §2 on branch
`attack/opus-cc-mac/pdd-3`.

## What is proved

`references_guarded_decidable` — the boolean check decides the honest
property. `Guarded` is stated as the ABSENCE OF A CYCLE, never as the
check restated: `Document.ReachPlus` is the transitive closure of the
bare-edge relation as an inductive relation, and a cycle is
`ReachPlus a a`. The check is a fuel-bounded search whose fuel is the
table's own size, and the two halves of the theorem are the two things
a door owes:

- SOUNDNESS (`guarded → Guarded`): a settled name lies on no cycle,
  because a cycle would let the settling fuel descend forever
  (`reachPlus_descends`).
- COMPLETENESS (`Guarded → guarded`): a name that does not settle
  within the table's size admits a bare path longer than the table has
  entries, so two of its nodes coincide (`nodup_length_le`, the
  pigeonhole) and the segment between them is a cycle.

Completeness is where the fuel bound earns its exact value: the failure
path visits `fuel + 1` names that all have entries, so `fuel = |table|`
is precisely enough to force a repeat and no more.

The address discipline is NOT here, and neither is resolvability — see
`Ast.reference`. A dangling name has no outgoing edge, so it lies on no
cycle and the decision is well defined without it.
-/

namespace Cas.Schema

/-! ## The non-suspend edge generator -/

mutual

/-- The table names a code mentions at positions NO `susp` guards.

The `.susp` arm answers `[]` — the walk stops at the guard, and that
single line is what makes "every cycle passes through a `susp`" and
"the non-suspend relation is acyclic" the same statement. -/
def Ast.bareRefs : Ast → List String
  | .reference n => [n]
  | .susp _ => []
  | .arr a => a.bareRefs
  | .struct fs => bareRefsFields fs
  | .decl _ _ ps => bareRefsParams ps
  | .union ms _ => bareRefsMembers ms
  | .tuple e es r => bareRefsElement e ++ bareRefsElements es ++ bareRefsRest r
  | _ => []

def bareRefsFields : List (String × Bool × Ast) → List String
  | [] => []
  | (_, _, a) :: fs => a.bareRefs ++ bareRefsFields fs

def bareRefsParams : List Ast → List String
  | [] => []
  | a :: as => a.bareRefs ++ bareRefsParams as

def bareRefsMembers : List Ast → List String
  | [] => []
  | a :: as => a.bareRefs ++ bareRefsMembers as

def bareRefsElement : Bool × Ast → List String
  | (_, a) => a.bareRefs

def bareRefsElements : List (Bool × Ast) → List String
  | [] => []
  | e :: es => bareRefsElement e ++ bareRefsElements es

def bareRefsRest : Option Ast → List String
  | none => []
  | some a => a.bareRefs

end

/-- A guard hides everything under it: a `susp` contributes no bare
edge, whatever its thunk mentions. Stated once, because it is the whole
content of the word "guarded". -/
theorem bareRefs_susp (a : Ast) : (Ast.susp a).bareRefs = [] := rfl

/-- A reference contributes exactly its own name. -/
theorem bareRefs_reference (n : String) : (Ast.reference n).bareRefs = [n] :=
  rfl

/-! ## The document -/

/-- Effect's single-root representation document, as content: the
references table and the root code.

The table is a LIST, not a map, because the canonical spelling is a
JSON object and its key order is part of the bytes. `Document.WF` asks
for strict name order for exactly the reason `.struct` asks it of
fields: it is what makes the spelling unique. -/
structure Document where
  references : List (String × Ast)
  representation : Ast

/-- The table's names, in the order the table carries them. -/
def Document.names (d : Document) : List String := d.references.map (·.1)

/-- The code one name stands for, if the table carries it. -/
def Document.lookup (d : Document) (n : String) : Option Ast :=
  (d.references.find? (·.1 == n)).map (·.2)

/-- The bare successors of one name: the names its entry mentions at
unguarded positions. A name with no entry has none, which is what makes
a dangling reference harmless to this decision. -/
def Document.out (d : Document) (n : String) : List String :=
  match d.lookup n with
  | some a => a.bareRefs
  | none => []

/-- One non-suspend edge of the table. -/
def Document.Edge (d : Document) (n m : String) : Prop := m ∈ d.out n

/-- The transitive closure of the bare-edge relation, as an inductive
relation — so a cycle is `ReachPlus a a` and needs no list surgery to
state. -/
inductive Document.ReachPlus (d : Document) : String → String → Prop
  | edge {n m : String} : d.Edge n m → d.ReachPlus n m
  | step {n m p : String} : d.Edge n m → d.ReachPlus m p → d.ReachPlus n p

/-- A cycle: a name that reaches itself along one or more bare edges. -/
def Document.Cyclic (d : Document) : Prop := ∃ a, d.ReachPlus a a

/-- GUARDED: no cycle of the non-suspend relation.

Because `bareRefs` stops at every `.susp`, this says exactly what the
ruling says — every cycle of the references table passes through a
`susp` — and it says it without mentioning the decision procedure. -/
def Document.Guarded (d : Document) : Prop := ¬ d.Cyclic

/-! ## The decision procedure -/

/-- The fuel-bounded search: does every bare path out of `n` run out
within `fuel` steps?

At zero fuel the only settled names are the ones with no bare successor
at all, so `settles k n` says "every bare path from `n` has at most `k`
edges". The recursion is structural on the fuel, so there is no
termination question. -/
def Document.settles (d : Document) : Nat → String → Bool
  | 0, n => (d.out n).isEmpty
  | fuel + 1, n => (d.out n).all (fun m => d.settles fuel m)

/-- THE CHECK, and THE DOOR: every table name settles within the
table's own size.

The fuel is `|table|` and not a constant: completeness needs a bound
that forces a repeated name, and the number of entries is exactly that
bound. -/
def Document.guarded (d : Document) : Bool :=
  d.names.all (fun n => d.settles d.references.length n)

/-! ## Soundness — a settled name lies on no cycle -/

/-- A name with an outgoing bare edge has a table entry. -/
theorem Document.lookup_of_edge {d : Document} {n m : String}
    (h : d.Edge n m) : ∃ a, d.lookup n = some a := by
  unfold Document.Edge Document.out at h
  cases hl : d.lookup n with
  | none => rw [hl] at h; simp at h
  | some a => exact ⟨a, rfl⟩

/-- And therefore it is one of the table's names: a cycle can only run
through entries the table actually carries. -/
theorem Document.mem_names_of_edge {d : Document} {n m : String}
    (h : d.Edge n m) : n ∈ d.names := by
  obtain ⟨a, ha⟩ := d.lookup_of_edge h
  unfold Document.lookup at ha
  simp only [Option.map_eq_some_iff] at ha
  obtain ⟨e, he, _⟩ := ha
  have hkey : e.1 = n := by
    have := List.find?_some he
    simpa using this
  exact hkey ▸ List.mem_map_of_mem (f := (·.1)) (List.mem_of_find?_eq_some he)

/-- One step of the search, read backwards: if `n` settles with fuel to
spare, every bare successor settles with one less.

Zero fuel is impossible here — a settled name at zero fuel has no
successors at all — which is why the conclusion can promise `j < fuel`
rather than `j ≤ fuel`. -/
theorem Document.settles_step {d : Document} {n m : String} {fuel : Nat}
    (he : d.Edge n m) (hs : d.settles fuel n = true) :
    ∃ j, j < fuel ∧ d.settles j m = true := by
  cases fuel with
  | zero =>
    unfold Document.settles at hs
    unfold Document.Edge at he
    simp only [List.isEmpty_iff] at hs
    rw [hs] at he
    simp at he
  | succ j =>
    refine ⟨j, Nat.lt_succ_self j, ?_⟩
    unfold Document.settles at hs
    exact List.all_eq_true.mp hs m he

/-- Reaching descends the fuel: if `n` settles and `n` reaches `m`, then
`m` settles at strictly less fuel. This is the whole of soundness —
along a cycle it says a settled name settles at strictly less fuel than
itself, and no natural number does that. -/
theorem Document.reachPlus_descends {d : Document} {n m : String} :
    d.ReachPlus n m → ∀ {fuel : Nat}, d.settles fuel n = true →
      ∃ j, j < fuel ∧ d.settles j m = true := by
  intro h
  induction h with
  | edge he => intro fuel hs; exact d.settles_step he hs
  | step he _ ih =>
    intro fuel hs
    obtain ⟨j, hj, hjs⟩ := d.settles_step he hs
    obtain ⟨i, hi, his⟩ := ih hjs
    exact ⟨i, Nat.lt_trans hi hj, his⟩

/-- A name on a cycle settles at NO fuel whatsoever. Infinite descent,
run as strong induction: a settling fuel would give a smaller one. -/
theorem Document.not_settles_of_cycle {d : Document} {a : String}
    (hc : d.ReachPlus a a) : ∀ fuel, d.settles fuel a = false := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    cases hs : d.settles fuel a with
    | false => rfl
    | true =>
      obtain ⟨j, hj, hjs⟩ := d.reachPlus_descends hc hs
      rw [ih j hj] at hjs
      exact absurd hjs (by simp)

/-! ## Completeness — an unsettled name lies on a cycle

The pigeonhole, then the extraction. -/

/-- A walk along bare edges, as the list of names it visits. -/
def Document.Walk (d : Document) : List String → Prop
  | [] => True
  | [_] => True
  | n :: m :: rest => d.Edge n m ∧ d.Walk (m :: rest)

/-- Everything a walk reaches after its head, it reaches. -/
theorem Document.walk_reachPlus {d : Document} :
    ∀ {x : String} {rest : List String}, d.Walk (x :: rest) →
      ∀ {y : String}, y ∈ rest → d.ReachPlus x y
  | _, [], _, _, hy => absurd hy (by simp)
  | x, m :: rest, hw, y, hy => by
    obtain ⟨he, hrest⟩ := hw
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact .edge he
    · exact .step he (d.walk_reachPlus hrest hy')

/-- A walk that repeats a name contains a cycle: the repeat reaches
itself. -/
theorem Document.walk_dup_cycle {d : Document} :
    ∀ {l : List String}, d.Walk l → ¬ l.Nodup → ∃ a, d.ReachPlus a a
  | [], _, hnd => absurd List.nodup_nil hnd
  | [_], _, hnd => absurd (by simp) hnd
  | x :: m :: rest, hw, hnd => by
    by_cases hx : x ∈ m :: rest
    · exact ⟨x, d.walk_reachPlus hw hx⟩
    · have : ¬ (m :: rest).Nodup := fun h => hnd (List.nodup_cons.mpr ⟨hx, h⟩)
      exact d.walk_dup_cycle hw.2 this

/-- THE PIGEONHOLE, proved here because the toolchain is core Lean with
no Mathlib: a duplicate-free list drawn from `s` is no longer than `s`.

The induction erases the head from `s` at every step, which is what
turns "no duplicates" into a length bound. -/
theorem nodup_length_le : ∀ {l s : List String}, l.Nodup →
    (∀ x ∈ l, x ∈ s) → l.length ≤ s.length
  | [], _, _, _ => Nat.zero_le _
  | a :: l, s, hnd, hsub => by
    have hmem : a ∈ s := hsub a (List.mem_cons_self ..)
    have hnd' := List.nodup_cons.mp hnd
    have hsub' : ∀ x ∈ l, x ∈ s.erase a := by
      intro x hx
      have hne : x ≠ a := fun h => hnd'.1 (h ▸ hx)
      exact (List.mem_erase_of_ne hne).mpr (hsub x (List.mem_cons_of_mem _ hx))
    have hlen := nodup_length_le hnd'.2 hsub'
    have herase : (s.erase a).length + 1 = s.length := by
      rw [List.length_erase_of_mem hmem]
      exact Nat.succ_pred_eq_of_pos (List.length_pos_of_mem hmem)
    simp only [List.length_cons]
    omega

/-- An unsettled name admits a bare walk of exactly the failed fuel's
length, and every name on it — the start included — has a table entry.

That last clause is what makes the fuel bound exact: the walk's names
are drawn from the table, so `fuel = |table|` gives one more name than
the table has entries. -/
theorem Document.settles_false_walk {d : Document} :
    ∀ (fuel : Nat) (n : String), d.settles fuel n = false →
      n ∈ d.names ∧ ∃ p : List String, p.length = fuel ∧
        d.Walk (n :: p) ∧ ∀ x ∈ p, x ∈ d.names
  | 0, n, hs => by
    unfold Document.settles at hs
    simp only [List.isEmpty_eq_false_iff_exists_mem] at hs
    obtain ⟨m, hm⟩ := hs
    exact ⟨d.mem_names_of_edge hm, [], rfl, trivial, by simp⟩
  | fuel + 1, n, hs => by
    unfold Document.settles at hs
    simp only [List.all_eq_false, Bool.not_eq_true] at hs
    obtain ⟨m, hm, hmf⟩ := hs
    obtain ⟨hmn, p, hlen, hwalk, hall⟩ := d.settles_false_walk fuel m hmf
    refine ⟨d.mem_names_of_edge hm, m :: p, by simp [hlen], ⟨hm, hwalk⟩, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hmn
    · exact hall x hx'

/-! ## The theorem -/

/-- `references_guarded_decidable` — THE C6 theorem. The fuel-bounded search
whose fuel is the table's size decides the absence of a cycle in the
non-suspend edge relation; equivalently, since `bareRefs` stops at every
guard, it decides that every cycle of the references table passes
through a `susp`.

Decidability is the content: `Guarded` is stated as the absence of a
cycle and never as the procedure restated, so the two directions are the
two things a door owes — it refuses nothing sound, and it admits nothing
unsound.

No `LAW SM-<n>:` line, deliberately. The guardedness ruling
(2026-08-30) has no row in the ruling registry (`tools/Laws.lean`), and
minting one is an operator act, not a builder's — a theorem that claims
an id belonging to another ruling is exactly the status lie the law
index exists to catch. OWED: the registry row, after which this
docstring gains its clause. -/
theorem references_guarded_decidable (d : Document) :
    d.guarded = true ↔ d.Guarded := by
  constructor
  · -- SOUNDNESS. A cycle's name is a table name, so the check settled
    -- it; but a name on a cycle settles at no fuel at all.
    intro hg hcy
    obtain ⟨a, hcyc⟩ := hcy
    have hmem : a ∈ d.names := by
      cases hcyc with
      | edge he => exact d.mem_names_of_edge he
      | step he _ => exact d.mem_names_of_edge he
    have hs := List.all_eq_true.mp hg a hmem
    rw [d.not_settles_of_cycle hcyc d.references.length] at hs
    exact absurd hs (by simp)
  · -- COMPLETENESS, by contraposition: an unsettled name walks further
    -- than the table has entries, so it repeats a name, and the repeat
    -- is a cycle.
    intro hguard
    cases hg : d.guarded with
    | true => rfl
    | false =>
      exfalso
      unfold Document.guarded at hg
      simp only [List.all_eq_false, Bool.not_eq_true] at hg
      obtain ⟨n, _, hns⟩ := hg
      obtain ⟨hnn, p, hlen, hwalk, hall⟩ :=
        d.settles_false_walk d.references.length n hns
      have hsub : ∀ x ∈ n :: p, x ∈ d.names := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hnn
        · exact hall x hx'
      have hnames : d.names.length = d.references.length := by
        simp [Document.names]
      have hnotnodup : ¬ (n :: p).Nodup := by
        intro hnd
        have hle := nodup_length_le hnd hsub
        simp only [List.length_cons, hlen, hnames] at hle
        omega
      exact hguard (d.walk_dup_cycle hwalk hnotnodup)

/-- The decision, as an instance — so `Guarded` can be used where a
decidable proposition is wanted without re-deriving the theorem. -/
instance (d : Document) : Decidable d.Guarded :=
  decidable_of_iff _ (references_guarded_decidable d)

/-! ## The walk the door runs — the same decision, each name once

`Document.settles` above re-walks every path. On a table whose entries
each name the next one twice, that is `Θ(2ⁿ)`: the break pass measured
302 915 ms on an ACYCLIC 25-entry table whose payload is 7 657 bytes
(`contracts/attacks/PDD-3/Attack.lean` §5, branch
`attack/opus-cc-mac/pdd-3`). This is the ingestion door for foreign
content, so the input is attacker-chosen.

`settleAll` is the same decision with the memo the packet's `DECREASES`
clause always described: it carries the names already known to settle
and consults that list before descending, so a name is explored once
however many paths reach it. The variant is `|dom(R)| - |visited|`, and
it is now a fact about the code.

The memo is FUEL-FREE on purpose. A name enters `seen` only after its
whole subtree settled, so membership means "no bare path out of this
name goes on forever" — a property of the table, not of the fuel that
happened to be left when the walk got there. That is what makes a hit
at one fuel sound at another. A name on a cycle never enters `seen`,
because it is added only on the way back out. -/

/-- The memoized walk. `seen` is the names already settled; `ns` is the
work left. Answers the grown memo, or `none` when a bare path out of
some name outruns the fuel. -/
def Document.settleAll (d : Document) :
    Nat → List String → List String → Option (List String)
  | _, seen, [] => some seen
  | 0, seen, n :: ns =>
    if seen.contains n then d.settleAll 0 seen ns
    else if (d.out n).isEmpty then d.settleAll 0 (n :: seen) ns
    else none
  | fuel + 1, seen, n :: ns =>
    if seen.contains n then d.settleAll (fuel + 1) seen ns
    else
      match d.settleAll fuel seen (d.out n) with
      | some s => d.settleAll (fuel + 1) (n :: s) ns
      | none => none
termination_by fuel _ ns => (fuel, ns.length)

/-- THE CHECK THE DOOR RUNS: every table name settles, each explored
once. Fuel is the table's own size, exactly as in `Document.guarded` —
`guardedMemo_eq_guarded` is what says the memo changed the schedule and
not the answer. -/
def Document.guardedMemo (d : Document) : Bool :=
  (d.settleAll d.references.length [] d.names).isSome

/-! ### The memo agrees with the walk

Three growth lemmas, an invariant, and a completeness lemma. The
recursion is lexicographic — the fuel falls when the walk descends, the
worklist shortens when it does not — so every proof below is strong
induction on the fuel with an inner induction on the worklist,
generalized over the memo. -/

/-- Settling, as a fuel-free property: SOME fuel settles the name. This
is the memo's invariant, and it is the reason a hit is sound at a fuel
other than the one that filled it. -/
def Document.Settling (d : Document) (n : String) : Prop :=
  ∃ k, d.settles k n = true

/-- One more step of fuel never unsettles a name. -/
theorem Document.settles_succ {d : Document} :
    ∀ (fuel : Nat) (n : String),
      d.settles fuel n = true → d.settles (fuel + 1) n = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hs
    unfold Document.settles at hs ⊢
    simp only [List.isEmpty_iff] at hs
    simp [hs]
  | succ f ih =>
    intro n hs
    unfold Document.settles at hs ⊢
    exact List.all_eq_true.mpr fun m hm => ih m (List.all_eq_true.mp hs m hm)

/-- And neither does any amount of it. -/
theorem Document.settles_mono {d : Document} :
    ∀ {f g : Nat} {n : String},
      f ≤ g → d.settles f n = true → d.settles g n = true := by
  intro f g
  induction g with
  | zero => intro n h hs; exact (Nat.le_zero.mp h) ▸ hs
  | succ g ih =>
    intro n h hs
    rcases Nat.lt_or_ge f (g + 1) with hlt | hge
    · exact d.settles_succ g n (ih (Nat.lt_succ_iff.mp hlt) hs)
    · exact (Nat.le_antisymm h hge) ▸ hs

/-- A finite list of settling names settles at ONE fuel — the largest of
theirs. Needed because the memo's invariant is per name and the step
that settles a parent needs one bound for all its children. -/
theorem Document.settles_uniform {d : Document} :
    ∀ (ms : List String), (∀ m ∈ ms, d.Settling m) →
      ∃ k, ∀ m ∈ ms, d.settles k m = true
  | [], _ => ⟨0, by simp⟩
  | m :: ms, h => by
    obtain ⟨k₁, hk₁⟩ := h m (List.mem_cons_self ..)
    obtain ⟨k₂, hk₂⟩ :=
      d.settles_uniform ms fun x hx => h x (List.mem_cons_of_mem _ hx)
    refine ⟨max k₁ k₂, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact d.settles_mono (Nat.le_max_left _ _) hk₁
    · exact d.settles_mono (Nat.le_max_right _ _) (hk₂ x hx')

/-- A name whose bare successors all settle, settles. -/
theorem Document.settling_of_out {d : Document} {n : String}
    (h : ∀ m ∈ d.out n, d.Settling m) : d.Settling n := by
  obtain ⟨k, hk⟩ := d.settles_uniform (d.out n) h
  exact ⟨k + 1, List.all_eq_true.mpr fun m hm => hk m hm⟩

/-- The memo only grows, and it covers the work it was given. Both
halves at once, because the induction is the same one. -/
theorem Document.settleAll_grows {d : Document} :
    ∀ (fuel : Nat) (seen ns S : List String),
      d.settleAll fuel seen ns = some S →
        (∀ x ∈ seen, x ∈ S) ∧ (∀ n ∈ ns, n ∈ S) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ihf =>
    intro seen ns
    induction ns generalizing seen with
    | nil =>
      intro S h
      simp only [Document.settleAll, Option.some.injEq] at h
      subst h
      exact ⟨fun _ hx => hx, by simp⟩
    | cons n ns ihn =>
      intro S h
      match fuel with
      | 0 =>
        unfold Document.settleAll at h
        split at h
        · next hc =>
          obtain ⟨hseen, hns⟩ := ihn seen S h
          exact ⟨hseen, fun x hx =>
            match List.mem_cons.mp hx with
            | .inl he => he ▸ hseen n (List.mem_of_elem_eq_true hc)
            | .inr hm => hns x hm⟩
        · split at h
          · obtain ⟨hseen, hns⟩ := ihn (n :: seen) S h
            refine ⟨fun x hx => hseen x (List.mem_cons_of_mem _ hx), fun x hx => ?_⟩
            rcases List.mem_cons.mp hx with rfl | hm
            · exact hseen x (List.mem_cons_self ..)
            · exact hns x hm
          · exact absurd h (by simp)
      | f + 1 =>
        unfold Document.settleAll at h
        split at h
        · next hc =>
          obtain ⟨hseen, hns⟩ := ihn seen S h
          exact ⟨hseen, fun x hx =>
            match List.mem_cons.mp hx with
            | .inl he => he ▸ hseen n (List.mem_of_elem_eq_true hc)
            | .inr hm => hns x hm⟩
        · split at h
          · next s hs =>
            obtain ⟨hsub, _⟩ := ihf f (Nat.lt_succ_self f) seen (d.out n) s hs
            obtain ⟨hseen, hns⟩ := ihn (n :: s) S h
            refine ⟨fun x hx => hseen x (List.mem_cons_of_mem _ (hsub x hx)),
              fun x hx => ?_⟩
            rcases List.mem_cons.mp hx with rfl | hm
            · exact hseen x (List.mem_cons_self ..)
            · exact hns x hm
          · exact absurd h (by simp)

/-- THE MEMO'S INVARIANT: everything in it settles. Proved against the
fuel-free `Settling`, which is what makes a hit at one fuel sound at
another. -/
theorem Document.settleAll_settling {d : Document} :
    ∀ (fuel : Nat) (seen ns S : List String),
      (∀ x ∈ seen, d.Settling x) →
        d.settleAll fuel seen ns = some S → ∀ x ∈ S, d.Settling x := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ihf =>
    intro seen ns
    induction ns generalizing seen with
    | nil =>
      intro S hinv h
      simp only [Document.settleAll, Option.some.injEq] at h
      subst h
      exact hinv
    | cons n ns ihn =>
      intro S hinv h
      match fuel with
      | 0 =>
        unfold Document.settleAll at h
        split at h
        · exact ihn seen S hinv h
        · split at h
          · next he =>
            refine ihn (n :: seen) S (fun x hx => ?_) h
            rcases List.mem_cons.mp hx with rfl | hm
            · exact ⟨0, by unfold Document.settles; exact he⟩
            · exact hinv x hm
          · exact absurd h (by simp)
      | f + 1 =>
        unfold Document.settleAll at h
        split at h
        · exact ihn seen S hinv h
        · split at h
          · next s hs =>
            have hsub := (d.settleAll_grows f seen (d.out n) s hs).2
            have hsettling := ihf f (Nat.lt_succ_self f) seen (d.out n) s hinv hs
            refine ihn (n :: s) S (fun x hx => ?_) h
            rcases List.mem_cons.mp hx with rfl | hm
            · exact d.settling_of_out fun m hm => hsettling m (hsub m hm)
            · exact hsettling x hm
          · exact absurd h (by simp)

/-- COMPLETENESS OF THE MEMO: work that settles within the fuel is work
the memoized walk finishes, whatever it has already seen. -/
theorem Document.settleAll_isSome {d : Document} :
    ∀ (fuel : Nat) (seen ns : List String),
      (∀ n ∈ ns, d.settles fuel n = true) →
        (d.settleAll fuel seen ns).isSome = true := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ihf =>
    intro seen ns
    induction ns generalizing seen with
    | nil => intro _; simp [Document.settleAll]
    | cons n ns ihn =>
      intro hall
      have hn := hall n (List.mem_cons_self ..)
      have hrest : ∀ m ∈ ns, d.settles fuel m = true :=
        fun m hm => hall m (List.mem_cons_of_mem _ hm)
      match fuel with
      | 0 =>
        unfold Document.settleAll
        split
        · exact ihn seen hrest
        · unfold Document.settles at hn
          simp only [hn, if_true]
          exact ihn (n :: seen) hrest
      | f + 1 =>
        unfold Document.settleAll
        split
        · exact ihn seen hrest
        · have hout : ∀ m ∈ d.out n, d.settles f m = true := by
            unfold Document.settles at hn
            exact fun m hm => List.all_eq_true.mp hn m hm
          have := ihf f (Nat.lt_succ_self f) seen (d.out n) hout
          cases hs : d.settleAll f seen (d.out n) with
          | none => rw [hs] at this; exact absurd this (by simp)
          | some s => exact ihn (n :: s) hrest

/-- `references_guarded_decidable_memo` — THE C6 THEOREM over the
procedure the door actually runs. The statement is
`references_guarded_decidable`'s, verbatim: the memo changed the
schedule and not the answer.

SOUNDNESS is the invariant — everything the memo settled settles at
some fuel, and a name on a cycle settles at none. COMPLETENESS is
`settleAll_isSome` against the naive walk's own completeness, which is
where the fuel bound `|table|` still earns its exact value. -/
theorem references_guarded_decidable_memo (d : Document) :
    d.guardedMemo = true ↔ d.Guarded := by
  constructor
  · intro hm
    cases hS : d.settleAll d.references.length [] d.names with
    | none => rw [Document.guardedMemo, hS] at hm; exact absurd hm (by simp)
    | some S =>
      have hcover := (d.settleAll_grows d.references.length [] d.names S hS).2
      have hinv :=
        d.settleAll_settling d.references.length [] d.names S (by simp) hS
      rintro ⟨a, hcyc⟩
      have hmem : a ∈ d.names := by
        cases hcyc with
        | edge he => exact d.mem_names_of_edge he
        | step he _ => exact d.mem_names_of_edge he
      obtain ⟨k, hk⟩ := hinv a (hcover a hmem)
      rw [d.not_settles_of_cycle hcyc k] at hk
      exact absurd hk (by simp)
  · intro hG
    have hg := (references_guarded_decidable d).mpr hG
    unfold Document.guarded at hg
    exact d.settleAll_isSome d.references.length [] d.names
      fun n hn => List.all_eq_true.mp hg n hn

/-- The memo changed the SCHEDULE and not the answer — two booleans
deciding one proposition. -/
theorem Document.guardedMemo_eq_guarded (d : Document) :
    d.guardedMemo = d.guarded := by
  cases hm : d.guardedMemo with
  | true =>
    cases hg : d.guarded with
    | true => rfl
    | false =>
      exact absurd ((references_guarded_decidable d).mpr
        ((references_guarded_decidable_memo d).mp hm)) (by simp [hg])
  | false =>
    cases hg : d.guarded with
    | true =>
      exact absurd ((references_guarded_decidable_memo d).mpr
        ((references_guarded_decidable d).mp hg)) (by simp [hm])
    | false => rfl

/-! ### The cost witness

The break pass's own blowup table, kept as a witness: `fanOutTable n`
has `n+1` entries, each naming the next one TWICE. It is ACYCLIC, so
the door walks the whole thing and then admits — which is why the
naive walk's `Θ(2ⁿ)` is a door problem and not a refusal problem. The
sizes below are past where the naive walk can go: at 25 entries it took
302 915 ms, and every entry doubles it. -/

/-- One fan entry: two fields, both naming the next name. -/
def fanOut (i : Nat) : String × Ast :=
  (s!"n{i}", .struct [("x", false, .reference s!"n{i + 1}"),
                      ("y", false, .reference s!"n{i + 1}")])

/-- `n + 1` entries, the last one a plain string, rooted at the first. -/
def fanOutTable (n : Nat) : Document :=
  { references := (List.range n).map fanOut ++ [(s!"n{n}", .str)],
    representation := .reference "n0" }

#guard (fanOutTable 30).references.length == 31
#guard (fanOutTable 30).guardedMemo

-- And the two agree at a size the naive walk can still be run at, so
-- `guardedMemo_eq_guarded` is checked and not only proved.
#guard (fanOutTable 8).guarded == (fanOutTable 8).guardedMemo

/-! ## The document's projection

The same revision-1 shape `Ast.representationDocument` writes, with the
table filled in. A single-root document with an empty table projects
byte-identically to the bare code's, so nothing already addressed
moves. -/

/-- The references table as a canonical JSON object. -/
def referencesToJson : List (String × Ast) → List (String × Json.Value)
  | [] => []
  | (n, a) :: rest => (n, a.toRepresentationJson) :: referencesToJson rest

/-- Effect's single-root persistent representation document, table and
all. -/
def Document.representationDocument (d : Document) : Json.Value :=
  .obj [
    ("references", .obj (referencesToJson d.references)),
    ("representation", d.representation.toRepresentationJson)]

/-- The revision-1 schema-node envelope of a document. -/
def Document.envelope (d : Document) : Json.Value :=
  .obj [("revision", .nat schemaRevision), ("value", d.representationDocument)]

/-- THE canonical payload of a document. -/
def Document.payload (d : Document) : String :=
  Json.renderCompact d.envelope

/-- A code's own document is the code with an empty table, so every
law about documents specialises to the laws already proved about
codes — and the bytes of an already-addressed schema node do not move.

The empty-table document is `Ast.representationDocument` on the nose. -/
theorem Document.representationDocument_nil (a : Ast) :
    (Document.mk [] a).representationDocument = a.representationDocument :=
  rfl

/-- And so is its envelope, which is what keeps every committed schema
address where it was. -/
theorem Document.envelope_nil (a : Ast) :
    (Document.mk [] a).envelope = a.envelope := rfl

/-- The table's entries are canonically spelled, whatever their names. -/
theorem referencesToJson_canonical :
    ∀ (rs : List (String × Ast)),
      Cas.Json.CanonicalFields (referencesToJson rs)
  | [] => trivial
  | (_, a) :: rest =>
    ⟨toRepresentationJson_canonical a, referencesToJson_canonical rest⟩

/-- The table's key list is the document's name list, verbatim — so the
strict-order clause `Document.WF` asks of the names IS the canonicality
clause the encoder needs, and neither is restated in terms of the
other. -/
theorem referencesToJson_keys :
    ∀ (rs : List (String × Ast)),
      (referencesToJson rs).map (·.1) = rs.map (·.1)
  | [] => rfl
  | (_, _) :: rest => by
    simp only [referencesToJson, List.map_cons, referencesToJson_keys rest]

/-- The document is canonically spelled when its names are in strict
order — the one clause the encoder cannot supply by construction,
because the names are content. -/
theorem Document.representationDocument_canonical (d : Document)
    (hs : List.Pairwise (fun a b : String × Ast => a.1 < b.1) d.references) :
    d.representationDocument.Canonical :=
  ⟨List.pairwise_map.mp
      (by decide : List.Pairwise (· < ·) ["references", "representation"]),
    ⟨List.pairwise_map.mp
        (referencesToJson_keys d.references ▸ List.pairwise_map.mpr hs),
      referencesToJson_canonical d.references⟩,
    toRepresentationJson_canonical d.representation, trivial⟩

/-- And so is its envelope. -/
theorem Document.envelope_canonical (d : Document)
    (hs : List.Pairwise (fun a b : String × Ast => a.1 < b.1) d.references) :
    d.envelope.Canonical :=
  ⟨List.pairwise_map.mp
      (by decide : List.Pairwise (· < ·) ["revision", "value"]),
    trivial, d.representationDocument_canonical hs, trivial⟩

/-! ## The document decoder -/

/-- The references table decoder, preserving the table's order
verbatim — the normalizer is what puts it in canonical order, exactly
as it is for a struct's fields. -/
def ofReferencesJson :
    List (String × Json.Value) → Option (List (String × Ast))
  | [] => some []
  | (n, v) :: rest =>
    (Ast.ofRepresentationJson v).bind fun a =>
    (ofReferencesJson rest).map fun rs => (n, a) :: rs

/-- The document decoder: the table and the root, at the exact keys the
projection writes. -/
def Document.ofRepresentationDocument : Json.Value → Option Document
  | .obj [("references", .obj refs), ("representation", r)] =>
    (ofReferencesJson refs).bind fun rs =>
    (Ast.ofRepresentationJson r).map fun a => Document.mk rs a
  | _ => none

/-- The envelope decoder: revision 1 only, exactly as the bare-code
decoder reads it. -/
def Document.ofEnvelope : Json.Value → Option Document
  | .obj [("revision", .nat r), ("value", v)] =>
    if r = schemaRevision then Document.ofRepresentationDocument v else none
  | _ => none

/-- The revision-1 normal form of a document: the literal-null collapse
applied throughout, table included. -/
def Document.repNorm (d : Document) : Document :=
  { references := d.references.map (fun e => (e.1, e.2.repNorm)),
    representation := d.representation.repNorm }

/-- The table's round trip, one entry at a time. -/
theorem ofReferencesJson_referencesToJson :
    ∀ (rs : List (String × Ast)),
      ofReferencesJson (referencesToJson rs)
        = some (rs.map (fun e => (e.1, e.2.repNorm)))
  | [] => rfl
  | (n, a) :: rest => by
    simp only [referencesToJson, ofReferencesJson,
      ofRepresentationJson_toRepresentationJson a,
      ofReferencesJson_referencesToJson rest, Option.bind_some,
      Option.map_some, List.map_cons]

/-- THE document round trip: the decoder answers every projection with
the projected document's normal form — the same statement the bare code
already carries, one level up. -/
theorem Document.ofRepresentationDocument_representationDocument
    (d : Document) :
    Document.ofRepresentationDocument d.representationDocument
      = some d.repNorm := by
  simp only [Document.representationDocument,
    Document.ofRepresentationDocument, ofReferencesJson_referencesToJson,
    ofRepresentationJson_toRepresentationJson, Option.bind_some,
    Option.map_some, Document.repNorm]

/-- And through the envelope. -/
theorem Document.ofEnvelope_envelope (d : Document) :
    Document.ofEnvelope d.envelope = some d.repNorm := by
  show (if schemaRevision = schemaRevision then
      Document.ofRepresentationDocument d.representationDocument
    else none) = _
  rw [if_pos rfl, Document.ofRepresentationDocument_representationDocument]

end Cas.Schema
