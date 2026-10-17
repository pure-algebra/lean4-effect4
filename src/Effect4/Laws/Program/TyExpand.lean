import Effect4.Program.TyExpand
import Effect4.Laws.Program.TyDecls

/-!
# Laws of expansion: a declared name with no recursion abbreviates its expansion

`Ty.expand exps t` replaces each reference to a name that `exps` declares, at a position the
checker reads by shape, by the name's entry (`Program/TyExpand.lean`). Take a guarded table and
a table of expansions that solves it (`TyDecls.Expands`) and declares only its names. Membership
under the table at every type is then `Val.hasTy` at the type's expansion
(`memberIn_iff_expand`). So a table with no recursion is a set of abbreviations: a declared name
has exactly the members of its expansion, a type that names no declared name where the checker
reads by shape. A recursive table has no solution, and the theorem says nothing of it.

The argument reuses the fixed point of `Laws/Program/TyDecls.lean`. Read each declared name as
`Val.hasTy` at its expansion (`expandOracle`). The admission fold at that oracle is `Val.hasTy`
at the expansion (`cata_declAlg_expand`), because each question of a step expands with its type
(`obligations_expand`). So that oracle is a fixed point (`expandOracle_fixedPoint`). On a guarded
table every fixed point agrees with membership (`fixedPoint_agree_at`).

Placement (`AGENTS.md`, five points), shared by every theorem below:

1. Concept `store-typing` (concept 1 of `docs/core/semantics.md`), the property that membership
   under a table has one meaning: here, that a declared name with no recursion means its
   expansion.
2. Question: the claim `tydecls-expansion` (`tools/ProofGraph/Registry.lean`), whose pointer is
   `memberIn_iff_expand`. Each lemma below is a step of it, consumed by the next.
3. Reach: every value, type and allocation table; a guarded table, and a table of expansions that
   solves it and declares only its names. Decisions rows 124, 158, 400, 401 and 402 bound it.
4. Does not establish: anything of a recursive table; anything of `Fits` or a caller of the
   checker, which reads no table yet; formation of a table; anything of a target.
5. Unlocks: R3's named types. A `Modeled` type's reference has exactly the members of its code
   (`Modeled.memberIn_ref`, `Laws/Schema/Modeled.lean`), so the declaration table carries the
   application's named types with the meaning their codecs already have.
-/

namespace Effect4.Program
open Effect4 Effect4.Machine

/-! ## Each question of a step expands with its type -/

/-- A record frame's questions at a payload map of its field types. A step of
`obligations_expand`. -/
theorem namedPairs_map (f : Ty → Ty) :
    ∀ (cs : List (String × Bool × Ty)) (ns xs : List Val),
      namedPairs (cs.map fun q => (q.1, q.2.1, f q.2.2)) ns xs =
        (namedPairs cs ns xs).map (List.map fun p => (p.1, f p.2))
  | [], [], [] => rfl
  | [], [], _ :: _ => rfl
  | [], _ :: _, _ => rfl
  | (n, o, t) :: cs, [], [] => by
    simp only [List.map_cons, namedPairs]
    cases o with
    | true =>
      rw [if_pos rfl, if_pos rfl]
      exact namedPairs_map f cs [] []
    | false => rfl
  | (_, _, _) :: _, [], _ :: _ => rfl
  | (_, _, _) :: _, _ :: _, [] => by
    rename_i nv _
    cases nv <;> rfl
  | (n, o, t) :: cs, nv :: ns, x :: xs => by
    cases nv with
    | str m =>
      simp only [List.map_cons, namedPairs]
      split
      · rw [namedPairs_map f cs ns xs]
        cases namedPairs cs ns xs with
        | some qs => rfl
        | none => rfl
      · cases o with
        | true =>
          rw [if_pos rfl, if_pos rfl]
          exact namedPairs_map f cs (.str m :: ns) (x :: xs)
        | false => rfl
    | _ => rfl

/-- A tuple's questions at a map of its item types. A step of `obligations_expand`. -/
theorem itemPairs_map (f : Ty → Ty) :
    ∀ (ts : List Ty) (xs : List Val),
      itemPairs (ts.map f) xs = (itemPairs ts xs).map (List.map fun p => (p.1, f p.2))
  | [], [] => rfl
  | t :: ts, x :: xs => by
    simp only [List.map_cons, itemPairs]
    rw [itemPairs_map f ts xs]
    cases itemPairs ts xs with
    | some qs => rfl
    | none => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl

/-- A map's questions at a map of its key and value types. A step of `obligations_expand`. -/
theorem entryPairs_map (f : Ty → Ty) (key value : Ty) :
    ∀ es : List Val,
      entryPairs (f key) (f value) es =
        (entryPairs key value es).map (List.map fun p => (p.1, f p.2))
  | [] => rfl
  | e :: es => by
    cases e with
    | pair a x =>
      simp only [entryPairs]
      rw [entryPairs_map f key value es]
      cases entryPairs key value es with
      | some qs => rfl
      | none => rfl
    | _ => rfl

/-- A cause's questions at a map of its error type. A step of `obligations_expand`. -/
theorem causeObligations_map (f : Ty → Ty) (error : Ty) :
    ∀ rs : List (Reason Err Defect FiberId Ann),
      causeObligations (f error) rs =
        (causeObligations error rs).map (List.map fun p => (p.1, f p.2))
  | [] => rfl
  | r :: rs => by
    cases r with
    | fail e ann =>
      simp only [causeObligations]
      cases valOfErr e with
      | some x =>
        dsimp only
        rw [causeObligations_map f error rs]
        cases causeObligations error rs with
        | some qs => rfl
        | none => rfl
      | none => rfl
    | die d ann => exact causeObligations_map f error rs
    | interrupt w ann => exact causeObligations_map f error rs

/-- A leaf's step is its shape check, whatever its questions are mapped by. -/
theorem leaf_map (c : Bool) (g : Val × Ty → Val × Ty) :
    (if c then some [] else none) = (if c then some [] else none).map (List.map g) := by
  cases c with
  | true => rfl
  | false => rfl

/-- **Each question of a step expands with its type**: at a type that is no reference to a name
`exps` declares, the step of the expansion asks the step's questions, each at its type's
expansion. A step of `cata_declAlg_expand`. -/
theorem obligations_expand (exps : TyDecls) {m : Ty}
    (hm : ∀ n, m.refName? = some n → exps.body? n = none) (v : Val) (allocated : List String) :
    Val.obligations v (Ty.expand exps m) allocated =
      (Val.obligations v m allocated).map (List.map fun p => (p.1, Ty.expand exps p.2)) := by
  cases m with
  | handle n => exact leaf_map _ _
  | app n args =>
    show Val.obligations v ((exps.body? n).getD (.app n args)) allocated = _
    rw [hm n rfl]
    exact leaf_map false _
  | option inner => cases v <;> rfl
  | list item =>
    cases v with
    | list xs =>
      show some (xs.map fun x => (x, Ty.expand exps item)) =
        Option.map _ (some (xs.map fun x => (x, item)))
      rw [Option.map_some, List.map_map]
      rfl
    | ctor i args =>
      rcases i with _ | _ | _ | _ | i
      · rfl
      · rfl
      · rfl
      · rcases args with _ | ⟨f, _ | ⟨g, rest⟩⟩
        · rfl
        · show Option.map _ (Val.snapshot? (.ctor 3 [f])) =
            Option.map _ (Option.map _ (Val.snapshot? (.ctor 3 [f])))
          cases Val.snapshot? (.ctor 3 [f]) with
          | none => rfl
          | some ids =>
            rw [Option.map_some, Option.map_some, Option.map_some, List.map_map]
            rfl
        · rfl
      · rfl
    | _ => rfl
  | prod a b =>
    cases v with
    | list xs =>
      rcases xs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;> rfl
    | _ => rfl
  | except e a =>
    cases v with
    | ctor i args =>
      rcases i with _ | _ | i <;> rcases args with _ | ⟨x, _ | ⟨y, rest⟩⟩ <;> rfl
    | _ => rfl
  | exitOf a e =>
    cases v with
    | ctor i args =>
      rcases i with _ | _ | i
      · rcases args with _ | ⟨x, _ | ⟨y, rest⟩⟩ <;> rfl
      · rcases args with _ | ⟨w, _ | ⟨y, rest⟩⟩
        · rfl
        · show (causeImage.ofVal w).bind _ = ((causeImage.ofVal w).bind _).map _
          cases causeImage.ofVal w with
          | none => rfl
          | some c => exact causeObligations_map (Ty.expand exps) e c.reasons
        · rfl
      · rfl
    | _ => rfl
  | causeOf e =>
    show (Val.cause? v).bind _ = ((Val.cause? v).bind _).map _
    cases Val.cause? v with
    | none => rfl
    | some c => exact causeObligations_map (Ty.expand exps) e c.reasons
  | union a b => rfl
  | record fs =>
    show (recordParts? v).bind (fun parts =>
        namedPairs (Ty.canon (Ty.expandFields exps fs)) parts.1 parts.2) =
      ((recordParts? v).bind fun parts => namedPairs (Ty.canon fs) parts.1 parts.2).map _
    rw [Ty.expandFields_eq_map]
    have hc : Ty.canon (fs.map fun q => (q.1, q.2.1, Ty.expand exps q.2.2)) =
        (Ty.canon fs).map fun q => (q.1, q.2.1, Ty.expand exps q.2.2) :=
      Field.canonBy_map (fun c : Bool × Ty => (c.1, Ty.expand exps c.2)) fs
    rw [hc]
    cases recordParts? v with
    | none => rfl
    | some parts => exact namedPairs_map (Ty.expand exps) (Ty.canon fs) parts.1 parts.2
  | map key value =>
    cases v with
    | list es =>
      show (if sortedEntries es then entryPairs (Ty.expand exps key) (Ty.expand exps value) es
          else none) = (if sortedEntries es then entryPairs key value es else none).map _
      cases sortedEntries es with
      | true => exact entryPairs_map (Ty.expand exps) key value es
      | false => rfl
    | _ => rfl
  | tuple ts =>
    cases v with
    | list xs =>
      show itemPairs (Ty.expandItems exps ts) xs = (itemPairs ts xs).map _
      rw [Ty.expandItems_eq_map]
      exact itemPairs_map (Ty.expand exps) ts xs
    | _ => rfl
  | never => rfl
  | unknown => rfl
  | unit => exact leaf_map _ _
  | nat => exact leaf_map _ _
  | int => exact leaf_map _ _
  | string => exact leaf_map _ _
  | bool => exact leaf_map _ _
  | lit s => exact leaf_map _ _
  | fiberOf a b => exact leaf_map _ _
  | refOf t => exact leaf_map _ _
  | deferredOf a b => exact leaf_map _ _
  | var i => rfl
  | null => exact leaf_map _ _
  | undefined => exact leaf_map _ _
  | number => exact leaf_map _ _
  | bytes => exact leaf_map _ _
  | contextOf keys => exact leaf_map _ _

/-! ## A union's members expand member by member -/

/-- **The members of an expansion** are the expansions' members of the type's members. A step of
`cata_declAlg_expand`. -/
theorem Ty.members_expand (exps : TyDecls) (t : Ty) :
    (Ty.expand exps t).members = t.members.flatMap fun m => (Ty.expand exps m).members := by
  induction t with
  | union a b iha ihb =>
    show (Ty.expand exps a).members ++ (Ty.expand exps b).members =
      (a.members ++ b.members).flatMap _
    rw [List.flatMap_append, iha, ihb]
  | never => rfl
  | _ => simp only [Ty.members, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The expansion of a member that is no reference to a name `exps` declares is a member: it
keeps its head. A step of `cata_declAlg_expand`. -/
theorem Ty.isMember_expand (exps : TyDecls) {m : Ty} (hm : m.isMember = true)
    (hfree : ∀ n, m.refName? = some n → exps.body? n = none) :
    (Ty.expand exps m).isMember = true := by
  cases m with
  | never => cases hm
  | union a b => cases hm
  | app n args =>
    show ((exps.body? n).getD (.app n args)).isMember = true
    rw [hfree n rfl]
    rfl
  | _ => rfl

/-! ## The fold at the expansions is `Val.hasTy` at the expansion -/

/-- **Each declared name read as `Val.hasTy` at its expansion.** -/
def expandOracle (exps : TyDecls) (name : String) : Adm := fun v allocated =>
  match exps.body? name with
  | some x => Val.hasTy v x allocated
  | none => false

/-- A reference to a declared name expands to the name's expansion. -/
theorem Ty.expand_of_unfold {decls exps : TyDecls} {m : Ty} {name : String} {body x : Ty}
    (hu : decls.unfold? m = some (name, body)) (hx : exps.body? name = some x) :
    Ty.expand exps m = x := by
  unfold TyDecls.unfold? at hu
  cases m with
  | app n args =>
    simp only [Ty.refName?, Option.bind_some] at hu
    cases hb : decls.body? n with
    | none =>
      rw [hb] at hu
      cases hu
    | some b =>
      rw [hb, Option.map_some] at hu
      cases hu
      show (exps.body? _).getD _ = x
      rw [hx]
      rfl
  | _ => cases hu

/-- A type the table does not unfold names no declared name, so no name `exps` declares when
`exps` declares only the table's names. -/
theorem free_of_unfold_none {decls exps : TyDecls} {m : Ty}
    (hdom : ∀ n x, exps.body? n = some x → (decls.body? n).isSome = true)
    (hu : decls.unfold? m = none) : ∀ n, m.refName? = some n → exps.body? n = none := by
  intro n hn
  unfold TyDecls.unfold? at hu
  rw [hn, Option.bind_some] at hu
  cases hb : decls.body? n with
  | some b =>
    rw [hb, Option.map_some] at hu
    cases hu
  | none =>
    cases hx : exps.body? n with
    | none => rfl
    | some x =>
      have h := hdom n x hx
      rw [hb] at h
      cases h

/-- A list's verdicts agree where their tests agree on its elements. -/
theorem all_congr_mem {α : Type} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.all_cons, List.all_cons, h x List.mem_cons_self,
      ih fun y hy => h y (List.mem_cons_of_mem x hy)]

/-- A list's answers agree where their tests agree on its elements. -/
theorem any_congr_mem {α : Type} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.any_cons, List.any_cons, h x List.mem_cons_self,
      ih fun y hy => h y (List.mem_cons_of_mem x hy)]

/-- **The fold at the expansions is `Val.hasTy` at the expansion**: each declared name read as
`Val.hasTy` at its expansion, the admission fold under the table admits what `Val.hasTy` admits at
the type's expansion. By induction on the value: a step's questions are at smaller values, and
each expands with its type (`obligations_expand`). A step of `memberIn_iff_expand`. -/
theorem cata_declAlg_expand {decls exps : TyDecls}
    (hdom : ∀ n x, exps.body? n = some x → (decls.body? n).isSome = true)
    (hcod : ∀ n b, decls.body? n = some b → (exps.body? n).isSome = true)
    (v : Val) (t : Ty) (allocated : List String) :
    (cata_ty (declAlg decls (expandOracle exps)) t).2 v allocated =
      Val.hasTy v (Ty.expand exps t) allocated := by
  rw [cata_declAlg_members, ← hasTy_members, Ty.members_expand, List.any_flatMap]
  refine any_congr_mem fun m hm => ?_
  rw [hasTy_members, cata_declAlg_step decls _ (Ty.members_isMember hm)]
  split
  · rename_i name body hu
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hcod name body (TyDecls.body?_of_unfold? hu))
    rw [Ty.expand_of_unfold hu hx]
    show expandOracle exps name v allocated = _
    unfold expandOracle
    rw [hx]
  · rename_i hu
    have hfree := free_of_unfold_none hdom hu
    rw [hasTy_eq_obligationsAll (Ty.isMember_expand exps (Ty.members_isMember hm) hfree)]
    unfold obligationsAll
    rw [obligations_expand exps hfree]
    cases hob : Val.obligations v m allocated with
    | none => rfl
    | some ps =>
      rw [Option.map_some]
      dsimp only
      rw [List.all_map]
      exact all_congr_mem fun p hp => cata_declAlg_expand hdom hcod p.1 p.2 allocated
termination_by sizeOf v
decreasing_by exact Val.sizeOf_obligation hob hp

/-- A solution gives each declared name an expansion. -/
theorem TyDecls.Expands.isSome {exps decls : TyDecls} (hs : TyDecls.Expands exps decls) :
    ∀ n b, decls.body? n = some b → (exps.body? n).isSome = true := by
  intro n b hb
  rw [hs (n, b) (TyDecls.mem_of_body? hb)]
  rfl

/-- **A solution is a fixed point**: each declared name read as `Val.hasTy` at its expansion
admits what the fold at that reading admits at the name's body. A step of `memberIn_iff_expand`. -/
theorem expandOracle_fixedPoint {decls exps : TyDecls} (hs : TyDecls.Expands exps decls)
    (hdom : ∀ n x, exps.body? n = some x → (decls.body? n).isSome = true) :
    FixedPoint decls (expandOracle exps) := by
  intro name body hb
  funext v allocated
  rw [cata_declAlg_expand hdom hs.isSome v body allocated]
  unfold expandOracle
  rw [hs (name, body) (TyDecls.mem_of_body? hb)]

/-- **A declared name with no recursion abbreviates its expansion** (claim `tydecls-expansion`).
Take a guarded table, and a table of expansions that solves it and declares only its names. Then
membership under the table at every type is `Val.hasTy` at the type's expansion. Proved from the
fixed point: the expansions are one (`expandOracle_fixedPoint`), and on a guarded table it agrees
with membership (`fixedPoint_agree_at`). Consumer: `memberIn_iff_expansions`, and
`Modeled.memberIn_ref`. -/
@[semantics "store-typing" (requirement := R3)]
theorem memberIn_iff_expand {decls exps : TyDecls} (hg : decls.guarded = true)
    (hs : TyDecls.Expands exps decls)
    (hdom : ∀ n x, exps.body? n = some x → (decls.body? n).isSome = true)
    {allocated : List String} {v : Val} {t : Ty} :
    MemberIn decls allocated v t ↔ Val.hasTy v (Ty.expand exps t) allocated = true := by
  rw [memberIn_iff_cata, fixedPoint_agree_at hg (checkerOracle_fixedPoint decls)
    (expandOracle_fixedPoint hs hdom) allocated v t,
    cata_declAlg_expand hdom hs.isSome v t allocated]

/-! ## The computed expansions, checked -/

/-- The names of the computed expansions, from any start: the start's, then the table's. -/
theorem TyDecls.names_foldl_expansions (decls acc : TyDecls) :
    (decls.foldl (fun acc d => acc ++ [(d.1, Ty.expand acc d.2)]) acc).map Prod.fst =
      acc.map Prod.fst ++ decls.map Prod.fst := by
  induction decls generalizing acc with
  | nil => rw [List.foldl_nil, List.map_nil, List.append_nil]
  | cons d ds ih =>
    rw [List.foldl_cons, ih, List.map_append, List.map_cons, List.map_cons, List.map_nil,
      List.append_assoc]
    rfl

/-- The computed expansions declare exactly the table's names. -/
theorem TyDecls.names_expansions (decls : TyDecls) :
    decls.expansions.map Prod.fst = decls.map Prod.fst := by
  unfold TyDecls.expansions
  rw [TyDecls.names_foldl_expansions, List.map_nil, List.nil_append]

/-- A name has an entry exactly when it is one of the table's names. -/
theorem TyDecls.body?_isSome_iff (decls : TyDecls) (name : String) :
    (decls.body? name).isSome = true ↔ name ∈ decls.map Prod.fst := by
  induction decls with
  | nil =>
    constructor
    · intro h
      cases h
    · intro h
      cases h
  | cons d ds ih =>
    obtain ⟨m, b⟩ := d
    unfold TyDecls.body? at ih ⊢
    simp only [List.lookup, List.map_cons, List.mem_cons]
    split
    · rename_i heq
      exact ⟨fun _ => Or.inl (beq_iff_eq.mp heq), fun _ => rfl⟩
    · rename_i hne
      rw [ih]
      refine ⟨Or.inr, fun h => h.elim (fun he => ?_) id⟩
      rw [beq_iff_eq.mpr he] at hne
      cases hne

/-- **The decided check is the solution's statement.** -/
theorem TyDecls.expands_of_expandsAll {exps decls : TyDecls} (h : exps.expandsAll decls = true) :
    TyDecls.Expands exps decls := by
  intro e he
  exact beq_iff_eq.mp (List.all_eq_true.mp h e he)

/-- **An expandable table's membership is `Val.hasTy` at its computed expansions.** The check
(`TyDecls.expandable`) decides the solution, and the computed expansions declare only the table's
names. Consumer: `Modeled.memberIn_ref`. -/
@[semantics "store-typing" (requirement := R3)]
theorem memberIn_iff_expansions {decls : TyDecls} (hg : decls.guarded = true)
    (he : decls.expandable = true) {allocated : List String} {v : Val} {t : Ty} :
    MemberIn decls allocated v t ↔
      Val.hasTy v (Ty.expand decls.expansions t) allocated = true := by
  refine memberIn_iff_expand hg (TyDecls.expands_of_expandsAll he) fun n x hx => ?_
  rw [TyDecls.body?_isSome_iff, ← TyDecls.names_expansions, ← TyDecls.body?_isSome_iff, hx]
  rfl

/-- **A consistent table reads each of its entries**: where no name has two bodies, a name's first
entry is every entry's. A step of `Modeled.memberIn_ref_of_lawful`. -/
theorem TyDecls.body?_of_consistent {decls : TyDecls}
    (hc : decls.Pairwise fun d e => d.1 = e.1 → d.2 = e.2) {e : String × Ty} (he : e ∈ decls) :
    decls.body? e.1 = some e.2 := by
  induction decls with
  | nil => cases he
  | cons d ds ih =>
    obtain ⟨m, b⟩ := d
    obtain ⟨hd, hds⟩ := List.pairwise_cons.mp hc
    unfold TyDecls.body? at ih ⊢
    simp only [List.lookup]
    split
    · rename_i heq
      rcases List.mem_cons.mp he with rfl | he'
      · rfl
      · exact congrArg some (hd e he' (beq_iff_eq.mp heq).symm)
    · rename_i hne
      rcases List.mem_cons.mp he with rfl | he'
      · dsimp only at hne
        rw [beq_iff_eq.mpr (rfl : m = m)] at hne
        cases hne
      · exact ih hds he'

end Effect4.Program
