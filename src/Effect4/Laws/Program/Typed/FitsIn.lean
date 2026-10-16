import Effect4.Laws.Program.TyDecls

/-!
# Membership in a typed world under a declaration table (D3's foundation)

`Fits w v t` (`Typed/Membership.lean`) reads a nominal reference `app n args` as a host handle,
so a value of a declared `Todo` never fits `Todo`. This module is the foundation of D3
(`docs/research/2026-10-16-math-d3/README.md`): membership in a world, with each declared name
read as its body, as the least fixed point. It is built beside `Fits` and edits nothing.

- `FitsAt decls w o`: one level of membership. Every arm is `Fits`'s, except a reference to a
  declared name, which reads the oracle `o` at the name. It is to `Fits` what `declAlg` is to
  `Val.hasTy` (`Laws/Program/TyDecls.lean`).
- `NamesClosed`: a reading of the names is closed when it reads a member of a name's body at
  the name.
- `NameFits`: the least closed reading, the intersection of every closed reading
  (Knaster–Tarski, impredicative in `Prop`, no fuel and no measure).
- `FitsIn decls w`: one level, with each declared name read at the least fixed point.

The laws:

- `fitsIn_nil`: at the empty table it is `Fits`, as an equality of propositions.
- `fitsIn_map`, `fitsIn_mono`: it moves along the world order, as `Fits` does.
- `fitsIn_unfold`: a reference to a declared name has exactly its body's members: the rule
  `MemberIn` has (`memberIn_unfold_iff`).
- `fitsIn_memberIn`: it implies the shape judgment under the table at the world's allocation
  table, as `fits_hasTy` does at the empty table (`memberIn_nil`).

Placement of the claims (`AGENTS.md`, five points), shared by every theorem below:

1. Concept `store-typing` (concept 1 of `docs/core/semantics.md`), the property that value
   membership in a world reads the application's declared names by their bodies, iso-recursively,
   and keeps `Fits`'s laws.
2. Question: the proposed claim `fits-declared` (D3's foundation). `fitsIn_nil` is its
   compatibility, `fitsIn_mono` its monotonicity, `fitsIn_unfold` its inversion and
   `fitsIn_memberIn` its agreement with the shape judgment.
3. Reach: every table, guarded or not; every world, value and type. Decisions rows 401, 402 and
   406 bound it.
4. Does not establish: the typed state at a non-empty table (M5 to M7 read `Fits`, which takes
   no table); the order or normalization under a table (`fits_sub`, `fits_normalize`); the
   converse of `fitsIn_memberIn` on capability-free types; a store's or a run's typing.
5. Unlocks: R3's open part "the wiring into `Fits`", and with it R9 at a non-empty table. The
   landing replaces `Fits` by `FitsIn` at the world's table.
-/

set_option autoImplicit false

namespace Effect4.Program.Typed
open Effect4.Machine Effect4.Program.Sched

mutual
/-- **One level of membership under a declaration table.** Every arm is `Fits`'s arm, with the
children read by `FitsAt` itself. A reference `app n args` to a declared name reads the oracle
`o` at the name; a reference to any other name reads the handle arm, as `Fits` does. -/
def FitsAt (decls : TyDecls) (w : World) (o : String → Val → Prop) (v : Val) : Ty → Prop
  | .never => False
  | .unit => match v with | .unit => True | _ => False
  | .nat => match v with | .nat _ => True | _ => False
  | .int => intImage v = true
  | .string => match v with | .str _ => True | _ => False
  | .bool => match v with | .bool _ => True | _ => False
  | .handle target =>
    match v with
    | .handle kind index => HandleFits w kind index target
    | Value.savedMask (.bool _) => target = Ty.maskRestoreTarget
    | _ => target = Ty.contextTarget ∧
        ∃ ctx, Val.context? v = some ctx ∧ ServicesFit w ctx.services ∧ Live w v
  | .option a =>
    match v with
    | .none => True
    | .some x => FitsAt decls w o x a
    | _ => False
  | .list a =>
    match v with
    | Value.fiberSnapshot _ =>
      match Val.snapshot? v with
      | some ids => ∀ id ∈ ids, FitsAt decls w o (Val.fiber id) a
      | none => False
    | .list values => ∀ x ∈ values, FitsAt decls w o x a
    | _ => False
  | .prod a b =>
    match v with
    | .list [x, y] => FitsAt decls w o x a ∧ FitsAt decls w o y b
    | _ => False
  | .except e a =>
    match v with
    | .ctor 0 [err] => FitsAt decls w o err e
    | .ctor 1 [val] => FitsAt decls w o val a
    | _ => False
  | .exitOf a e =>
    match v with
    | Val.exitOk x => FitsAt decls w o x a
    | Value.exitErr written =>
      match causeImage.ofVal written with
      | some c => CauseFits (fun x => FitsAt decls w o x e) c ∧ ShapeFree c
      | none => False
    | _ => False
  | .causeOf e =>
    match Val.cause? v with
    | some c => CauseFits (fun x => FitsAt decls w o x e) c
    | none => False
  | .fiberOf a e =>
    match v with
    | Value.fiber index => FiberDeclared w ⟨index⟩ a e
    | _ => False
  | .union l r => FitsAt decls w o v l ∨ FitsAt decls w o v r
  | .lit s => match v with | .str s' => s' = s | _ => False
  | .refOf t =>
    match v with
    | Value.cell index => RefDeclared w ⟨index⟩ t
    | _ => False
  | .deferredOf a e =>
    match v with
    | Value.promise index => PromiseDeclared w ⟨index⟩ a e
    | _ => False
  | .var _ => False
  | .unknown => Live w v
  | .record fs =>
    match recordParts? v with
    | some (ns, xs) => NamedFit (Ty.canon (fittersAt decls w o fs)) ns xs
    | none => False
  | .map k t =>
    match v with
    | .list es => EntriesFit (fun a => FitsAt decls w o a k) (fun x => FitsAt decls w o x t) es
    | _ => False
  | .tuple ts =>
    match v with
    | .list xs => ItemsFit (itemFittersAt decls w o ts) xs
    | _ => False
  | .app name _ =>
    match decls.body? name with
    | some _ => o name v
    | none =>
      match v with
      | .handle kind index => HandleFits w kind index name
      | Value.savedMask (.bool _) => name = Ty.maskRestoreTarget
      | _ => name = Ty.contextTarget ∧
          ∃ ctx, Val.context? v = some ctx ∧ ServicesFit w ctx.services ∧ Live w v
  | .null => match v with | .none => True | _ => False
  | .undefined => match v with | .unit => True | _ => False
  | .number => numberImage v = true
  | .bytes => match v with | .bytes _ => True | _ => False
  | .contextOf keys =>
    ∃ ctx, Val.context? v = some ctx ∧ ctx.services.Satisfies keys ∧
      ServicesFit w ctx.services ∧ Live w v ∧
      ∀ key ∈ keys.elems, ∃ carrier value,
        w.serviceTy key = some carrier ∧ ctx.services.getV key = some value ∧
          FlatFits w value carrier
/-- The field-list companion of `FitsAt`. -/
def fittersAt (decls : TyDecls) (w : World) (o : String → Val → Prop) :
    List (String × Bool × Ty) → List (String × Bool × (Val → Prop))
  | [] => []
  | (n, b, t) :: rest => (n, b, fun x => FitsAt decls w o x t) :: fittersAt decls w o rest
/-- The item-list companion of `FitsAt`. -/
def itemFittersAt (decls : TyDecls) (w : World) (o : String → Val → Prop) :
    List Ty → List (Val → Prop)
  | [] => []
  | t :: rest => (fun x => FitsAt decls w o x t) :: itemFittersAt decls w o rest
end

/-- A reading of the declared names is **closed** when it reads every member of a name's body at
the name. -/
def NamesClosed (decls : TyDecls) (w : World) (o : String → Val → Prop) : Prop :=
  ∀ name body v, decls.body? name = some body → FitsAt decls w o v body → o name v

/-- **The least closed reading** of the declared names: a value is read at a name when every
closed reading reads it there. It is the least fixed point of `o ↦ (n ↦ FitsAt … o · (body n))`
by the Knaster–Tarski construction; `FitsAt` is monotone in the oracle (`fitsAt_map`). -/
def NameFits (decls : TyDecls) (w : World) (name : String) (v : Val) : Prop :=
  ∀ o, NamesClosed decls w o → o name v

/-- **Membership under a declaration table**: one level of membership, with each declared name
read at the least fixed point. A value fits a declared name only through a finite derivation, as
`MemberIn` reads it. -/
def FitsIn (decls : TyDecls) (w : World) (v : Val) (t : Ty) : Prop :=
  FitsAt decls w (NameFits decls w) v t

/-! ## The companions as maps -/

/-- A field's predicate under an oracle. -/
def fitterAtOf (decls : TyDecls) (w : World) (o : String → Val → Prop) (c : Bool × Ty) :
    Bool × (Val → Prop) :=
  (c.1, fun x => FitsAt decls w o x c.2)

theorem fittersAt_eq_map (decls : TyDecls) (w : World) (o : String → Val → Prop)
    (fs : List (String × Bool × Ty)) :
    fittersAt decls w o fs = fs.map (fun q => (q.1, fitterAtOf decls w o q.2)) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, b, t⟩ := p
    rw [fittersAt, ih]
    rfl

theorem itemFittersAt_eq_map (decls : TyDecls) (w : World) (o : String → Val → Prop)
    (ts : List Ty) : itemFittersAt decls w o ts = ts.map (fun t x => FitsAt decls w o x t) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [itemFittersAt, ih]
    rfl

/-- The record arm, named: the canonical fields read by name. -/
theorem fitsAt_record (decls : TyDecls) (w : World) (o : String → Val → Prop) {v : Val}
    {ns xs : List Val} (hv : recordParts? v = some (ns, xs)) (fs : List (String × Bool × Ty)) :
    FitsAt decls w o v (.record fs) ↔
      NamedFit ((Ty.canon fs).map (fun q => (q.1, fitterAtOf decls w o q.2))) ns xs := by
  rw [FitsAt, hv, fittersAt_eq_map, Ty.canon, Field.canonBy_map]

/-- Nothing but a record value is a record's member. -/
theorem fitsAt_record_inv (decls : TyDecls) (w : World) (o : String → Val → Prop) (v : Val)
    (fs : List (String × Bool × Ty)) (h : FitsAt decls w o v (.record fs)) :
    ∃ ns xs, recordParts? v = some (ns, xs) ∧
      NamedFit ((Ty.canon fs).map (fun q => (q.1, fitterAtOf decls w o q.2))) ns xs := by
  cases hv : recordParts? v with
  | none =>
    rw [FitsAt, hv] at h
    exact h.elim
  | some parts =>
    obtain ⟨ns, xs⟩ := parts
    exact ⟨ns, xs, rfl, (fitsAt_record decls w o hv fs).mp h⟩

/-- The tuple arm. -/
theorem fitsAt_tuple (decls : TyDecls) (w : World) (o : String → Val → Prop) (xs : List Val)
    (ts : List Ty) :
    FitsAt decls w o (.list xs) (.tuple ts) ↔ ItemsFit (ts.map (fun t x => FitsAt decls w o x t)) xs := by
  rw [FitsAt, itemFittersAt_eq_map]

/-! ## At the empty table it is `Fits` -/

/-- **At the empty table, one level of membership is `Fits`, under every oracle**: no name is
declared, so the oracle is read nowhere and every arm is `Fits`'s. -/
theorem fitsAt_nil (w : World) (o : String → Val → Prop) :
    ∀ (t : Ty) (v : Val), FitsAt [] w o v t = Fits w v t := by
  intro t
  induction t with
  | option a ih => intro v; simp only [FitsAt, Fits, ih]; rfl
  | list a ih => intro v; simp only [FitsAt, Fits, ih]; rfl
  | prod a b iha ihb => intro v; simp only [FitsAt, Fits, iha, ihb]; rfl
  | except e a ihe iha => intro v; simp only [FitsAt, Fits, ihe, iha]; rfl
  | exitOf a e iha ihe => intro v; simp only [FitsAt, Fits, iha, ihe]; rfl
  | causeOf e ih => intro v; simp only [FitsAt, Fits, ih]; rfl
  | union l r ihl ihr => intro v; simp only [FitsAt, Fits, ihl, ihr]
  | map k t ihk iht => intro v; simp only [FitsAt, Fits, ihk, iht]; rfl
  | record fs ih =>
    intro v
    have hf : fittersAt [] w o fs = fitters w fs := by
      rw [fittersAt_eq_map, fitters_eq_map]
      refine List.map_congr_left fun q hq => ?_
      simp only [fitterAtOf, fitterOf, ih q hq]
    simp only [FitsAt, Fits, hf]; rfl
  | tuple ts ih =>
    intro v
    have hf : itemFittersAt [] w o ts = itemFitters w ts := by
      rw [itemFittersAt_eq_map, itemFitters_eq_map]
      refine List.map_congr_left fun t ht => ?_
      simp only [ih t ht]
    simp only [FitsAt, Fits, hf]; rfl
  | never | unit | nat | int | string | bool | handle | fiberOf | lit | refOf | deferredOf | var
    | unknown | app | null | undefined | number | bytes | contextOf => intro v; rfl

/-! ## Along the world order, and in the oracle -/

/-- **One level of membership moves to a later world and a larger oracle**: `fits_map`'s
induction, with the oracle carried at a declared name. -/
theorem fitsAt_map {decls : TyDecls} {w1 w2 : World} {o1 o2 : String → Val → Prop}
    (hg : Grows w1 w2) (ho : ∀ name v, o1 name v → o2 name v) :
    ∀ (t : Ty) (v : Val), FitsAt decls w1 o1 v t → FitsAt decls w2 o2 v t := by
  intro t
  induction t with
  | option a ih =>
    intro v h
    simp only [FitsAt] at h
    split at h
    · trivial
    · rename_i x
      exact ih x h
    · exact h.elim
  | list a ih =>
    intro v h
    simp only [FitsAt] at h
    split at h
    · rename_i p
      split at h
      · rename_i ids hids
        simp only [FitsAt, hids]
        exact fun id hid => ih _ (h id hid)
      · exact h.elim
    · rename_i values
      exact fun x hx => ih x (h x hx)
    · exact h.elim
  | prod a b iha ihb =>
    intro v h
    simp only [FitsAt] at h
    split at h
    · exact ⟨iha _ h.1, ihb _ h.2⟩
    · exact h.elim
  | except e a ihe iha =>
    intro v h
    simp only [FitsAt] at h
    split at h
    · exact ihe _ h
    · exact iha _ h
    · exact h.elim
  | exitOf a e iha ihe =>
    intro v h
    simp only [FitsAt] at h
    split at h
    · exact iha _ h
    · rename_i written
      split at h
      · rename_i c hc
        simp only [FitsAt, hc]
        exact ⟨causeFits_map (fun x hx => ihe x hx) h.1, h.2⟩
      · exact h.elim
    · exact h.elim
  | causeOf e ih =>
    intro v h
    simp only [FitsAt] at h
    split at h
    · rename_i c hc
      simp only [FitsAt, hc]
      exact causeFits_map (fun x hx => ih x hx) h
    · exact h.elim
  | union l r ihl ihr =>
    intro v h
    exact h.imp (ihl v) (ihr v)
  | record fs ih =>
    intro v h
    obtain ⟨ns, xs, hv, hfit⟩ := fitsAt_record_inv decls w1 o1 v fs h
    rw [fitsAt_record decls w2 o2 hv]
    refine namedFit_mono _ _ ns xs ?_ ?_ hfit
    · simp only [List.map_map]
      rfl
    · intro pq hpq
      rw [List.zip_map, List.mem_map] at hpq
      obtain ⟨⟨q1, q2⟩, hq, rfl⟩ := hpq
      have heq : q1 = q2 := Ty.mem_zip_self hq
      subst heq
      exact ⟨id, fun x hx => ih q1 (Ty.mem_canon (List.of_mem_zip hq).1) x hx⟩
  | map k t ihk iht =>
    intro v h
    simp only [FitsAt] at h
    split at h
    · rename_i es
      refine ⟨h.1, fun e he => ?_⟩
      have := h.2 e he
      cases e
      case pair a x => exact ⟨ihk a this.1, iht x this.2⟩
      all_goals exact this.elim
    · exact h.elim
  | tuple ts ih =>
    intro v h
    cases v
    case list xs =>
      rw [fitsAt_tuple] at h ⊢
      refine itemsFit_mono _ _ xs (by rw [List.length_map, List.length_map]) ?_ h
      intro pq hpq x hx
      rw [List.zip_map, List.mem_map] at hpq
      obtain ⟨⟨t1, t2⟩, ht, rfl⟩ := hpq
      have heq : t1 = t2 := Ty.mem_zip_self ht
      subst heq
      exact ih t1 (List.of_mem_zip ht).1 x hx
    all_goals exact h.elim
  | app name args _ =>
    intro v h
    simp only [FitsAt] at h ⊢
    split at h
    · exact ho name v h
    · exact hg.fits (t := .handle name) h
  | never => intro v h; exact h.elim
  | var _ => intro v h; exact h.elim
  | unit => intro v h; exact hg.fits (t := .unit) h
  | nat => intro v h; exact hg.fits (t := .nat) h
  | int => intro v h; exact hg.fits (t := .int) h
  | string => intro v h; exact hg.fits (t := .string) h
  | bool => intro v h; exact hg.fits (t := .bool) h
  | handle target => intro v h; exact hg.fits (t := .handle target) h
  | fiberOf a e _ _ => intro v h; exact hg.fits (t := .fiberOf a e) h
  | lit s => intro v h; exact hg.fits (t := .lit s) h
  | refOf a _ => intro v h; exact hg.fits (t := .refOf a) h
  | deferredOf a e _ _ => intro v h; exact hg.fits (t := .deferredOf a e) h
  | unknown => intro v h; exact hg.fits (t := .unknown) h
  | null => intro v h; exact hg.fits (t := .null) h
  | undefined => intro v h; exact hg.fits (t := .undefined) h
  | number => intro v h; exact hg.fits (t := .number) h
  | bytes => intro v h; exact hg.fits (t := .bytes) h
  | contextOf keys => intro v h; exact hg.fits (t := .contextOf keys) h

/-- One level of membership is monotone in the oracle, at a fixed world. -/
theorem fitsAt_oracle_mono {decls : TyDecls} {w : World} {o1 o2 : String → Val → Prop}
    (ho : ∀ name v, o1 name v → o2 name v) {t : Ty} {v : Val} (h : FitsAt decls w o1 v t) :
    FitsAt decls w o2 v t :=
  fitsAt_map (Grows.refl w) ho t v h

/-! ## The least fixed point -/

/-- The least closed reading is closed. -/
theorem nameFits_closed (decls : TyDecls) (w : World) : NamesClosed decls w (NameFits decls w) :=
  fun name body v hb hv o ho => ho name body v hb (fitsAt_oracle_mono (fun _ _ hu => hu o ho) hv)

/-- The least closed reading lies below every closed reading: the induction principle. -/
theorem nameFits_least {decls : TyDecls} {w : World} {o : String → Val → Prop}
    (ho : NamesClosed decls w o) {name : String} {v : Val} (h : NameFits decls w name v) :
    o name v :=
  h o ho

/-- **A declared name reads exactly its body's members**: the least closed reading is a fixed
point. -/
theorem nameFits_iff {decls : TyDecls} {w : World} {name : String} {body : Ty} {v : Val}
    (hb : decls.body? name = some body) : NameFits decls w name v ↔ FitsIn decls w v body := by
  constructor
  · intro h
    have hc : NamesClosed decls w fun n u => ∃ b, decls.body? n = some b ∧ FitsIn decls w u b := by
      intro n b u hnb hu
      refine ⟨b, hnb, fitsAt_oracle_mono ?_ hu⟩
      intro n' u' hu'
      obtain ⟨b', hb', hu'⟩ := hu'
      exact nameFits_closed decls w n' b' u' hb' hu'
    obtain ⟨b, hb', hv⟩ := nameFits_least hc h
    rw [hb] at hb'
    cases hb'
    exact hv
  · exact nameFits_closed decls w name body v hb

/-! ## The laws -/

/-- **At the empty table, membership under the table is `Fits`.** Placement: concept
`store-typing`, R3, the compatibility of the proposed claim `fits-declared`. Route: no name is
declared, so the reference arm reads the handle arm and the oracle is read nowhere
(`fitsAt_nil`). Consumer: the landing, where every statement over `Fits` becomes the empty-table
instance of one over `FitsIn`. -/
@[semantics "store-typing" (requirement := R3)]
theorem fitsIn_nil (w : World) (v : Val) (t : Ty) : FitsIn [] w v t = Fits w v t :=
  fitsAt_nil w _ t v

/-- **Iso-recursive unfolding**: a reference to a declared name has exactly its body's members,
at either reading of the reference. Placement: concept `store-typing`, R3, the inversion of the
proposed claim `fits-declared`; the rule `MemberIn` has (`memberIn_unfold_iff`). Route: the
reference arm reads the least fixed point, which is a fixed point (`nameFits_iff`). Consumer:
every elimination at a declared name in the landing: a field read, an update, a fold and a tag
dispatch under `Ty.headMembers`. -/
@[semantics "store-typing" (requirement := R3)]
theorem fitsIn_unfold {decls : TyDecls} {w : World} {v : Val} {t : Ty} {name : String}
    {body : Ty} (hu : decls.unfold? t = some (name, body)) :
    FitsIn decls w v t ↔ FitsIn decls w v body := by
  cases t
  case app n args =>
    have hb := TyDecls.body?_of_unfold? hu
    have hn : n = name := by
      simp only [TyDecls.unfold?, Ty.refName?, Option.bind_some, Option.map_eq_some_iff] at hu
      obtain ⟨_, _, h⟩ := hu
      exact (Prod.mk.inj h).1
    subst hn
    show FitsAt decls w (NameFits decls w) v (.app n args) ↔ _
    simp only [FitsAt, hb]
    exact nameFits_iff hb
  all_goals simp only [TyDecls.unfold?, Ty.refName?, Option.bind_none] at hu; cases hu

/-- **Membership under the table moves to a later world.** Placement: concept `store-typing`,
R3, the monotonicity of the proposed claim `fits-declared` (`fits-mono` under a table). Route:
the least fixed point at the earlier world lies below the later one's, by its induction principle
(`nameFits_least`) and `fitsAt_map` with the oracle fixed; then `fitsAt_map` with the world and
the oracle both moved. Consumer: `fitsIn_mono`, and the landing's `fits_mono`. -/
@[semantics "store-typing" (requirement := R3)]
theorem fitsIn_map {decls : TyDecls} {w1 w2 : World} (hg : Grows w1 w2) {t : Ty} {v : Val}
    (h : FitsIn decls w1 v t) : FitsIn decls w2 v t := by
  have hn : ∀ name u, NameFits decls w1 name u → NameFits decls w2 name u := by
    intro name u hu
    refine nameFits_least (fun n b x hb hx => ?_) hu
    exact nameFits_closed decls w2 n b x hb (fitsAt_map hg (fun _ _ hy => hy) b x hx)
  exact fitsAt_map hg hn t v h

/-- **Membership under the table is monotone under the host world order**: `fits_mono` at every
table. Placement: concept `store-typing`, R3, the monotonicity of the proposed claim
`fits-declared`. Route: `fitsIn_map` at the order's premises. Consumer: the landing's typed state,
where each step moves to a later world. -/
@[semantics "store-typing" (requirement := R3)]
theorem fitsIn_mono {decls : TyDecls} {w w' : World} (ordered : w.leHost w') {t : Ty} {v : Val}
    (h : FitsIn decls w v t) : FitsIn decls w' v t :=
  fitsIn_map ⟨ordered.1.2.1, ordered.1.2.2.1, ordered.1.2.2.2.1, ordered.2, ordered.1.1.2,
    le_serviceTy ordered.1⟩ h

/-! ## Agreement with the shape judgment under the table

A step of `MemberIn` asks one question per child of the value (`Val.obligations`). Each lemma
below reads one arm of `FitsAt` as the step's questions, each answered by the arm's predicate. -/

/-- A record's named read answers the step's questions: each named value at its field's type. -/
theorem namedPairs_of_namedFit (P : Ty → Val → Prop) :
    ∀ (cs : List (String × Bool × Ty)) (ns xs : List Val),
      NamedFit (cs.map fun c => (c.1, c.2.1, P c.2.2)) ns xs →
      ∃ ps, namedPairs cs ns xs = some ps ∧ ∀ p ∈ ps, (∃ c ∈ cs, c.2.2 = p.2) ∧ P p.2 p.1
  | [], [], [], _ => ⟨[], rfl, fun _ hp => absurd hp List.not_mem_nil⟩
  | [], [], _ :: _, h => h.elim
  | [], _ :: _, _, h => h.elim
  | (_, b, _) :: cs, [], [], h => by
    obtain ⟨hb, hr⟩ := h
    obtain ⟨ps, hps, hall⟩ := namedPairs_of_namedFit P cs [] [] hr
    refine ⟨ps, ?_, fun p hp => ?_⟩
    · rw [namedPairs, if_pos hb]
      exact hps
    · obtain ⟨⟨c, hc, hce⟩, hP⟩ := hall p hp
      exact ⟨⟨c, List.mem_cons_of_mem _ hc, hce⟩, hP⟩
  | _ :: _, [], _ :: _, h => h.elim
  | _ :: _, v0 :: _, [], h => by cases v0 <;> exact h.elim
  | (n, b, t) :: cs, v0 :: ns, x :: xs, h => by
    cases v0 with
    | str m =>
      simp only [List.map_cons, NamedFit] at h
      by_cases hm : m = n
      · rw [if_pos hm] at h
        obtain ⟨hx, hr⟩ := h
        obtain ⟨ps, hps, hall⟩ := namedPairs_of_namedFit P cs ns xs hr
        refine ⟨(x, t) :: ps, ?_, fun p hp => ?_⟩
        · simp only [namedPairs, if_pos hm, hps, Option.map_some]
        · rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨⟨(n, b, t), List.mem_cons_self, rfl⟩, hx⟩
          · obtain ⟨⟨c, hc, hce⟩, hP⟩ := hall p hp
            exact ⟨⟨c, List.mem_cons_of_mem _ hc, hce⟩, hP⟩
      · rw [if_neg hm] at h
        obtain ⟨hb, hr⟩ := h
        obtain ⟨ps, hps, hall⟩ := namedPairs_of_namedFit P cs (.str m :: ns) (x :: xs) hr
        refine ⟨ps, ?_, fun p hp => ?_⟩
        · simp only [namedPairs, if_neg hm, hb, if_true]
          exact hps
        · obtain ⟨⟨c, hc, hce⟩, hP⟩ := hall p hp
          exact ⟨⟨c, List.mem_cons_of_mem _ hc, hce⟩, hP⟩
    | _ => exact h.elim

/-- A tuple's items answer the step's questions: each item at its type. -/
theorem itemPairs_of_itemsFit (P : Ty → Val → Prop) :
    ∀ (ts : List Ty) (xs : List Val), ItemsFit (ts.map fun t x => P t x) xs →
      ∃ ps, itemPairs ts xs = some ps ∧ ∀ p ∈ ps, p.2 ∈ ts ∧ P p.2 p.1
  | [], [], _ => ⟨[], rfl, fun _ hp => absurd hp List.not_mem_nil⟩
  | t :: ts, x :: xs, h => by
    obtain ⟨hx, hr⟩ := h
    obtain ⟨ps, hps, hall⟩ := itemPairs_of_itemsFit P ts xs hr
    refine ⟨(x, t) :: ps, by simp only [itemPairs, hps, Option.map_some], fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨List.mem_cons_self, hx⟩
    · obtain ⟨hm, hP⟩ := hall p hp
      exact ⟨List.mem_cons_of_mem _ hm, hP⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- A map's entries answer the step's questions: each key at the key type, each value at the
value type. -/
theorem entryPairs_of_entries {PK PV : Val → Prop} (key value : Ty) :
    ∀ es : List Val, (∀ e ∈ es, match e with | .pair a x => PK a ∧ PV x | _ => False) →
      ∃ ps, entryPairs key value es = some ps ∧
        ∀ p ∈ ps, (p.2 = key ∧ PK p.1) ∨ (p.2 = value ∧ PV p.1)
  | [], _ => ⟨[], rfl, fun _ hp => absurd hp List.not_mem_nil⟩
  | e :: es, h => by
    have he := h e List.mem_cons_self
    obtain ⟨ps, hps, hall⟩ :=
      entryPairs_of_entries key value es fun e' he' => h e' (List.mem_cons_of_mem _ he')
    cases e
    case pair a x =>
      refine ⟨(a, key) :: (x, value) :: ps, by simp only [entryPairs, hps, Option.map_some],
        fun p hp => ?_⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · exact Or.inl ⟨rfl, he.1⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · exact Or.inr ⟨rfl, he.2⟩
      · exact hall p hp
    all_goals exact he.elim

/-- A cause whose typed failures fit answers the step's questions: each failure's value at the
error type. -/
theorem causeObligations_of_fit {P : Val → Prop} (error : Ty) :
    ∀ rs : List (Reason Err Defect FiberId Ann),
      (∀ r ∈ rs, match r with
        | .fail e _ => ∃ v, valOfErr e = some v ∧ P v
        | .die _ _ | .interrupt _ _ => True) →
      ∃ ps, causeObligations error rs = some ps ∧ ∀ p ∈ ps, p.2 = error ∧ P p.1
  | [], _ => ⟨[], rfl, fun _ hp => absurd hp List.not_mem_nil⟩
  | r :: rs, h => by
    have hr := h r List.mem_cons_self
    obtain ⟨ps, hps, hall⟩ :=
      causeObligations_of_fit error rs fun r' hr' => h r' (List.mem_cons_of_mem _ hr')
    cases r with
    | fail e ann =>
      obtain ⟨x, hx, hP⟩ := hr
      refine ⟨(x, error) :: ps, by simp only [causeObligations, hx, hps, Option.map_some],
        fun p hp => ?_⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨rfl, hP⟩
      · exact hall p hp
    | die d ann => exact ⟨ps, hps, hall⟩
    | interrupt i ann => exact ⟨ps, hps, hall⟩

/-- **One level of membership implies the shape judgment under the table**, when every declared
name the oracle reads is a member there: `fits_hasTy`'s statement, at every table. -/
theorem fitsAt_memberIn {decls : TyDecls} {w : World} {o : String → Val → Prop}
    (ho : ∀ name body v, decls.body? name = some body → o name v →
      ∀ args, MemberIn decls w.state.externals.allocated v (.app name args)) :
    ∀ (t : Ty) (v : Val), FitsAt decls w o v t → MemberIn decls w.state.externals.allocated v t := by
  intro t
  induction t with
  | never => intro v h; exact h.elim
  | var _ => intro v h; exact h.elim
  | option a ih =>
    intro v h
    simp only [FitsAt] at h
    split at h
    · exact .step rfl rfl fun _ hp => absurd hp List.not_mem_nil
    · rename_i x
      exact .step rfl rfl fun p hp => by
        rcases List.mem_singleton.mp hp with rfl
        exact ih x h
    · exact h.elim
  | list a ih =>
    intro v h
    simp only [FitsAt] at h
    split at h
    · rename_i p
      split at h
      · rename_i ids hids
        refine .step rfl (ps := ids.map fun id => (Val.fiber id, a)) ?_ ?_
        · unfold Val.obligations
          simp only [hids, Option.map_some]
        · intro q hq
          obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hq
          exact ih _ (h id hid)
      · exact h.elim
    · rename_i values
      refine .step rfl rfl fun q hq => ?_
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
      exact ih x (h x hx)
    · exact h.elim
  | prod a b iha ihb =>
    intro v h
    simp only [FitsAt] at h
    split at h
    · rename_i x y
      refine .step rfl rfl fun q hq => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact iha x h.1
      · exact ihb y h.2
    · exact h.elim
  | except e a ihe iha =>
    intro v h
    simp only [FitsAt] at h
    split at h
    · rename_i x
      exact .step rfl rfl fun q hq => by
        rcases List.mem_singleton.mp hq with rfl
        exact ihe x h
    · rename_i x
      exact .step rfl rfl fun q hq => by
        rcases List.mem_singleton.mp hq with rfl
        exact iha x h
    · exact h.elim
  | exitOf a e iha ihe =>
    intro v h
    simp only [FitsAt] at h
    split at h
    · rename_i x
      exact .step rfl rfl fun q hq => by
        rcases List.mem_singleton.mp hq with rfl
        exact iha x h
    · rename_i written
      split at h
      · rename_i c hc
        obtain ⟨ps, hps, hall⟩ := causeObligations_of_fit e c.reasons h.1
        refine .step rfl (ps := ps) ?_ fun q hq => ?_
        · unfold Val.obligations
          simp only [hc, Option.bind_some]
          exact hps
        · obtain ⟨he, hq⟩ := hall q hq
          rw [he]
          exact ihe q.1 hq
      · exact h.elim
    · exact h.elim
  | causeOf e ih =>
    intro v h
    simp only [FitsAt] at h
    split at h
    · rename_i c hc
      obtain ⟨ps, hps, hall⟩ := causeObligations_of_fit e c.reasons h
      refine .step rfl (ps := ps) ?_ fun q hq => ?_
      · unfold Val.obligations
        simp only [hc, Option.bind_some]
        exact hps
      · obtain ⟨he, hq⟩ := hall q hq
        rw [he]
        exact ih q.1 hq
    · exact h.elim
  | union l r ihl ihr =>
    intro v h
    rcases h with h | h
    · exact .left (ihl v h)
    · exact .right (ihr v h)
  | record fs ih =>
    intro v h
    obtain ⟨ns, xs, hv, hfit⟩ := fitsAt_record_inv decls w o v fs h
    obtain ⟨ps, hps, hall⟩ :=
      namedPairs_of_namedFit (fun t x => FitsAt decls w o x t) (Ty.canon fs) ns xs hfit
    refine .step rfl (ps := ps) ?_ fun q hq => ?_
    · unfold Val.obligations
      simp only [hv, Option.bind_some]
      exact hps
    · obtain ⟨⟨c, hc, hce⟩, hq⟩ := hall q hq
      rw [← hce] at hq ⊢
      exact ih c (Ty.mem_canon hc) q.1 hq
  | map k t ihk iht =>
    intro v h
    simp only [FitsAt] at h
    split at h
    · rename_i es
      obtain ⟨hs, he⟩ := h
      obtain ⟨ps, hps, hall⟩ := entryPairs_of_entries (PK := fun a => FitsAt decls w o a k)
        (PV := fun x => FitsAt decls w o x t) k t es he
      refine .step rfl (ps := ps) ?_ fun q hq => ?_
      · unfold Val.obligations
        simp only [hs, if_true]
        exact hps
      · rcases hall q hq with ⟨he, hq⟩ | ⟨he, hq⟩
        · rw [he]
          exact ihk q.1 hq
        · rw [he]
          exact iht q.1 hq
    · exact h.elim
  | tuple ts ih =>
    intro v h
    cases v
    case list xs =>
      rw [fitsAt_tuple] at h
      obtain ⟨ps, hps, hall⟩ := itemPairs_of_itemsFit (fun t x => FitsAt decls w o x t) ts xs h
      refine .step rfl hps fun q hq => ?_
      obtain ⟨hm, hq⟩ := hall q hq
      exact ih q.2 hm q.1 hq
    all_goals exact h.elim
  | app name args _ =>
    intro v h
    simp only [FitsAt] at h
    split at h
    · rename_i body hb
      exact ho name body v hb h args
    · rename_i hb
      have hu : decls.unfold? (.app name args) = none := by
        simp only [TyDecls.unfold?, Ty.refName?, Option.bind_some, hb, Option.map_none]
      exact memberIn_of_hasTy hu rfl (handle_fits_hasTy w (target := name) h)
  | unit => intro v h; exact memberIn_of_hasTy rfl rfl (fits_hasTy w .unit v h)
  | nat => intro v h; exact memberIn_of_hasTy rfl rfl (fits_hasTy w .nat v h)
  | int => intro v h; exact memberIn_of_hasTy rfl rfl (fits_hasTy w .int v h)
  | string => intro v h; exact memberIn_of_hasTy rfl rfl (fits_hasTy w .string v h)
  | bool => intro v h; exact memberIn_of_hasTy rfl rfl (fits_hasTy w .bool v h)
  | handle target => intro v h; exact memberIn_of_hasTy rfl rfl (fits_hasTy w (.handle target) v h)
  | fiberOf a e _ _ => intro v h; exact memberIn_of_hasTy rfl rfl (fits_hasTy w (.fiberOf a e) v h)
  | lit s => intro v h; exact memberIn_of_hasTy rfl rfl (fits_hasTy w (.lit s) v h)
  | refOf a _ => intro v h; exact memberIn_of_hasTy rfl rfl (fits_hasTy w (.refOf a) v h)
  | deferredOf a e _ _ =>
    intro v h; exact memberIn_of_hasTy rfl rfl (fits_hasTy w (.deferredOf a e) v h)
  | unknown => intro v h; exact memberIn_of_hasTy rfl rfl (fits_hasTy w .unknown v h)
  | null => intro v h; exact memberIn_of_hasTy rfl rfl (fits_hasTy w .null v h)
  | undefined => intro v h; exact memberIn_of_hasTy rfl rfl (fits_hasTy w .undefined v h)
  | number => intro v h; exact memberIn_of_hasTy rfl rfl (fits_hasTy w .number v h)
  | bytes => intro v h; exact memberIn_of_hasTy rfl rfl (fits_hasTy w .bytes v h)
  | contextOf keys =>
    intro v h; exact memberIn_of_hasTy rfl rfl (fits_hasTy w (.contextOf keys) v h)

/-- **Membership under the table implies the shape judgment under the table**, at the world's
allocation table. Placement: concept `store-typing`, R3, the agreement of the proposed claim
`fits-declared` with `MemberIn`. Route: the least fixed point lies below the reading "a member of
every reference to the name", which is closed by `MemberIn`'s unfold rule; then
`fitsAt_memberIn`. At the empty table it is `fits_hasTy` (`fitsIn_nil`, `memberIn_nil`).
Consumer: the landing's stored-cell typing (`ValueOk` under the table) and its
`heapTable_of_fits`. -/
@[semantics "store-typing" (requirement := R3)]
theorem fitsIn_memberIn {decls : TyDecls} {w : World} {v : Val} {t : Ty}
    (h : FitsIn decls w v t) : MemberIn decls w.state.externals.allocated v t := by
  have hc : NamesClosed decls w fun n u =>
      ∀ args, MemberIn decls w.state.externals.allocated u (.app n args) := by
    intro n b u hb hu args
    refine .unfold (name := n) (body := b) ?_ (fitsAt_memberIn (fun _ _ _ _ hx => hx) b u hu)
    simp only [TyDecls.unfold?, Ty.refName?, Option.bind_some, hb, Option.map_some]
  exact fitsAt_memberIn (fun _ _ u _ hu => nameFits_least hc hu) t v h

/-! ## The rest of D3, as planned goals

Each goal below is a statement the landing consumes, over the definitions of this module. The
landing replaces `Fits` by `FitsIn` at the world's table, so each goal is the table form of a law
that `Typed/Membership.lean` or `Typed/Denotation/Terms.lean` proves at the empty table. -/

/-- **The order is sound for membership under the table** (planned goal): `fits_sub` at every
table. Placement: concept `store-typing`, R3, a step of the proposed claim `fits-declared`
(`fits-subn` under a table). Reach: `Ty.sub`, every table, world and value. Route: `fits_sub`'s
induction over `FitsAt` with the oracle fixed. The one new arm is a reference to a declared name:
`Ty.sub` compares a name with the same name only, so both ends read one oracle answer, as
`declAlg_admitsSub` reads one admission. It does not establish `Ty.subN` (the goal
`fitsIn_normalize` gives it). Consumer: the landing's `fits_sub` and every typing rule that
widens. -/
@[semantics "store-typing" (requirement := R3)]
proof_goal fitsIn_sub (decls : TyDecls) (w : World) (a b : Ty) (v : Val) :
    Ty.sub a b = true → FitsIn decls w v a → FitsIn decls w v b

/-- **Membership under the table is invariant under normalization** (planned goal):
`fits_normalize` at every table. Placement: concept `store-typing`, R3, a step of the proposed
claim `fits-declared` (`fits-normalize` under a table). Reach: every table, world, value and type.
Route: `fits_normalize`'s induction over `FitsAt`; normalization keeps a reference's name and maps
its arguments (decisions row 406 (1)), and the reference arm reads the name alone, as
`cata_declAlg_normalize` reads it. Consumer: the landing's `fits_normalize` and `fits_subN`. -/
@[semantics "store-typing" (requirement := R3)]
proof_goal fitsIn_normalize (decls : TyDecls) (w : World) (t : Ty) (v : Val) :
    FitsIn decls w v t.normalize ↔ FitsIn decls w v t

/-- **A member under the table is live** (planned goal): `fits_live` at every table. Placement:
concept `store-typing`, R3, a step of the proposed claim `fits-declared`. Reach: every table,
world, value and type. Route: the least fixed point lies below the reading "the value is live"
(`nameFits_least`), which is closed by `fits_live`'s induction over `FitsAt` with that oracle.
Consumer: the landing's `fits_live`, which `Live` at `unknown` and the stores' validity read. -/
@[semantics "store-typing" (requirement := R3)]
proof_goal fitsIn_live (decls : TyDecls) (w : World) (t : Ty) (v : Val) :
    FitsIn decls w v t → Live w v

/-- **Membership under the table reads the union members under the table** (planned goal): the
`FitsIn` form of `memberIn_iff_membersIn`. Placement: concept `store-typing`, R3, a step of the
proposed claim `fits-declared`. Reach: every table, world, value and type. Route: the goal
`fitsIn_normalize`, then the head members: a union member reads its sides (`fits_members`'s
argument over `FitsAt`), and a reference to a declared name unfolds (`fitsIn_unfold`). A
reference met again before a value constructor adds no member; the cut is `hasTyIn_absorb`'s,
by the induction principle `nameFits_least`. Consumer: the four readers of the term typer under
the table (a field read, an update, a fold, a tag dispatch), each the existing law at a head
member. -/
@[semantics "store-typing" (requirement := R3)]
proof_goal fitsIn_iff_membersIn (decls : TyDecls) (w : World) (t : Ty) (v : Val) :
    FitsIn decls w v t ↔ ∃ x ∈ Ty.membersIn decls t, FitsIn decls w v x

/-- **Term progress under the table** (planned goal): `evalTerm_progress` without its premise
`sig.types = []`. A term that the term typer types under the signature's table, over values that
fit their types under the same table, evaluates, and its value fits the term's type. Placement:
concept `store-typing`, R9, the step of the typed state that the 41 premises `types = []` of
the term laws guard (`docs/research/2026-10-16-math-d3/README.md` §3). Reach: every signature
whose atoms are the native table's, every world, environment and term. Route:
`evalTerm_progress`'s induction; a field read, an update and a fold read their target through
the goal `fitsIn_iff_membersIn` and fold a written field through `fitsIn_unfold`; each atom's law
(`atomFits`) is restated over `FitsAt`. It does not establish the typed state at a
non-empty table: that is the landing, which replaces `Fits` by `FitsIn` in `J`. Consumer: the
landing's term laws, `evalTerm_fits`, `termMaps_of_typed` and the library's operation laws. -/
@[semantics "store-typing" (requirement := R9)]
proof_goal evalTerm_progressIn (sig : Signature NativeOp) (w : World) (vals : List Val)
    (env : List Ty) (t : Term) (ty : Ty) :
    sig.atomOf = nativeAtomTy → env.length = vals.length →
    (∀ (i : Nat) (a : Ty) (x : Val), env[i]? = some a → vals[i]? = some x →
      FitsIn sig.types w x a) →
    termTy sig env t = some ty → ∃ v, evalTerm vals t = some v ∧ FitsIn sig.types w v ty

end Effect4.Program.Typed
