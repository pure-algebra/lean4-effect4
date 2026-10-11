import Effect4.Laws.Codegen.ReadLeaf

/-!
# Codegen.Services — a block's services read back (decisions rows 338 and 339, slice CO-6b)

A block's roles declare its services (`DefRole`), and the printer prints each as its key and its
layer after the definitions (`printServices`, `src/Effect4/Codegen/Print.lean`). The reader gives
the roles back from the layers (`roleOf`, `src/Effect4/Codegen/Read.lean`). This module proves the
three facts that the round trip of a block uses (`readModule_printModule_defs`,
`Laws/Codegen/Module.lean`):

- the printed service constants are plain, are service constants, and carry no layer path
  (`printServices_ok`), so the reader finds them where the printer put them;
- the printed layers read back as the services' information (`printServices_ok`);
- that information gives each definition its role (`roleOf_servicesOf`), at a block whose
  services print, so whose names are distinct when it has a service (`serviceFault`).

Placement: concept `exact-codecs`, compatibility: steps of the claim `module-defs-round-trip`;
requirement R8. They say nothing of tsgo or of rc.112.
-/

set_option autoImplicit false

namespace Effect4.Program

variable {Op : Type}

/-! ## Membership -/

/-- A method of a service is a definition with that method's role. -/
theorem mem_serviceMethods {s : String} {defs : List DefDecl} {x : String × Nat × Nat} :
    x ∈ serviceMethods s defs ↔ ∃ d, defs[x.2.1]? = some d ∧ d.role = .serviceMethod s x.1 x.2.2 := by
  obtain ⟨m, j, n⟩ := x
  simp only [serviceMethods, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨j', -, h⟩
    unfold methodAt at h
    split at h
    · rename_i d hd
      split at h
      · rename_i s' m' n' hrole
        split at h
        · rename_i hs
          cases h
          exact ⟨d, hd, by rw [hrole, hs]⟩
        · cases h
      · cases h
    · cases h
  · rintro ⟨d, hd, hrole⟩
    refine ⟨j, (List.getElem?_eq_some_iff.mp hd).1, ?_⟩
    show methodAt s defs j = some (m, j, n)
    unfold methodAt
    rw [hd]
    dsimp only
    rw [hrole]
    exact if_pos rfl

/-- A service of a block is a definition with the role of its initial program. -/
theorem mem_servicesOf {defs : List DefDecl} {sv : Service} :
    sv ∈ servicesOf defs ↔ ∃ d, defs[sv.init]? = some d ∧ d.role = .serviceInit sv.name ∧
      sv.methods = serviceMethods sv.name defs := by
  obtain ⟨s, i, methods⟩ := sv
  simp only [servicesOf, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨i', -, h⟩
    unfold serviceAt at h
    split at h
    · rename_i d hd
      split at h
      · rename_i s' hrole
        cases h
        exact ⟨d, hd, hrole, rfl⟩
      · cases h
    · cases h
  · rintro ⟨d, hd, hrole, hmethods⟩
    refine ⟨i, (List.getElem?_eq_some_iff.mp hd).1, ?_⟩
    show serviceAt defs i = some ⟨s, i, methods⟩
    unfold serviceAt
    rw [hd]
    dsimp only
    rw [hrole, hmethods]

/-- Definitions with distinct names at two positions with one name are at one position. -/
theorem index_eq_of_name {defs : List DefDecl} (nodup : (defs.map (·.name)).Nodup) {i j : Nat}
    {d d' : DefDecl} (hi : defs[i]? = some d) (hj : defs[j]? = some d') (hname : d.name = d'.name) :
    i = j := by
  obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.mp hj
  have hil : i < (defs.map (·.name)).length := by rw [List.length_map]; exact hi'
  have hjl : j < (defs.map (·.name)).length := by rw [List.length_map]; exact hj'
  exact (List.getElem_inj (h₀ := hil) (h₁ := hjl) nodup).mp
    (by rw [List.getElem_map, List.getElem_map]; exact hname)

/-! ## What the printer prints -/

/-- What a printed layer gives back of a service: its name, its initial program's name, and each
method's name, definition name and arity. -/
def serviceInfo (defs : List DefDecl) (sv : Service) :
    String × String × List (String × String × Nat) :=
  (sv.name, ((defs[sv.init]?).map (·.name)).getD "",
    sv.methods.map fun x => (x.1, ((defs[x.2.1]?).map (·.name)).getD "", x.2.2))

/-- A list that `mapM` maps without failing keeps its length. -/
theorem length_of_mapM_ok {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r → r.length = l.length
  | [], r, h => by
    cases h
    rfl
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, -, rest⟩ := bind_eq_ok.mp h
    obtain ⟨bs, hbs, heq⟩ := bind_eq_ok.mp rest
    cases heq
    exact congrArg Nat.succ (length_of_mapM_ok hbs)

/-- `arity` argument types read off a request. -/
theorem length_methodArgTys : ∀ (n : Nat) (t : Ty) {tys : List Ty},
    methodArgTys n t = some tys → tys.length = n
  | 0, _, tys, h => by
    cases h
    rfl
  | 1, _, tys, h => by
    cases h
    rfl
  | n + 2, .prod a b, tys, h => by
    simp only [methodArgTys] at h
    obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.mp h
    exact congrArg Nat.succ (length_methodArgTys (n + 1) b hrest)
  | _ + 2, .never, _, h | _ + 2, .unit, _, h | _ + 2, .nat, _, h | _ + 2, .int, _, h
  | _ + 2, .string, _, h | _ + 2, .bool, _, h | _ + 2, .handle _, _, h
  | _ + 2, .option _, _, h | _ + 2, .list _, _, h | _ + 2, .except _ _, _, h
  | _ + 2, .exitOf _ _, _, h | _ + 2, .causeOf _, _, h | _ + 2, .fiberOf _ _, _, h
  | _ + 2, .union _ _, _, h | _ + 2, .lit _, _, h | _ + 2, .refOf _, _, h
  | _ + 2, .deferredOf _ _, _, h | _ + 2, .var _, _, h | _ + 2, .unknown, _, h
  | _ + 2, .record _, _, h | _ + 2, .map _ _, _, h | _ + 2, .tuple _, _, h
  | _ + 2, .app _ _, _, h | _ + 2, .null, _, h | _ + 2, .undefined, _, h
  | _ + 2, .number, _, h | _ + 2, .bytes, _, h => by cases h

/-- A method's arguments are `arity` many. -/
theorem length_methodArgs {state : Ty} {d : DefDecl} {n : Nat} {tys : List Ty}
    (h : methodArgs state d n = some tys) : tys.length = n := by
  unfold methodArgs at h
  split at h
  · split at h
    · cases h
      rfl
    · cases h
  · split at h
    · exact length_methodArgTys _ _ h
    · cases h
  · cases h

/-- The closures of a printed layer read back as its methods' information. -/
theorem readServiceMethods_ok {defs : List DefDecl} {init : DefDecl} :
    ∀ {methods : List (String × Nat × Nat)} {closures : List (String × TypeScript.Expr)},
      methods.mapM (methodClosure init defs) = .ok closures →
        closures.mapM readServiceMethod =
          some (methods.map fun x => (x.1, ((defs[x.2.1]?).map (·.name)).getD "", x.2.2))
  | [], closures, h => by
    cases h
    rfl
  | x :: rest, closures, h => by
    rw [List.mapM_cons] at h
    obtain ⟨c, hc, tail⟩ := bind_eq_ok.mp h
    obtain ⟨cs, hcs, heq⟩ := bind_eq_ok.mp tail
    cases heq
    obtain ⟨m, j, n⟩ := x
    unfold methodClosure at hc
    dsimp only at hc
    cases hd : defs[j]? with
    | none =>
      rw [hd] at hc
      cases hc
    | some d =>
      rw [hd] at hc
      dsimp only at hc
      cases htys : methodArgs init.answer d n with
      | none =>
        rw [htys] at hc
        cases hc
      | some tys =>
        rw [htys] at hc
        obtain ⟨params, hparams, heq⟩ := bind_eq_ok.mp hc
        cases heq
        have hlen : params.length = n := by
          rw [length_of_mapM_ok hparams, List.length_zip, length_methodArgs htys]
          simp only [argNames, List.length_map, List.length_range, Nat.min_self]
        rw [List.mapM_cons, readServiceMethods_ok hcs]
        simp only [readServiceMethod, hlen, hd, Option.map_some, Option.getD_some, List.map_cons]
        rfl

/-- **A printed service**: its key and its layer, both plain service constants named for the
service, and the layer reads back as the service's information. -/
theorem printService_ok {sig : Signature Op} {defs : List DefDecl} {sv : Service}
    {cs : List TypeScript.ConstDecl} (h : printService sig defs sv = .ok cs) :
    ∃ key layer, cs = [key, layer] ∧ key.type = none ∧ key.exported = true ∧
      layer.type = none ∧ layer.exported = true ∧ isServiceConst key = true ∧
      isServiceConst layer = true ∧ key.name = sv.name ∧ layer.name = sv.name ++ "Layer" ∧
      readServiceLayer key = none ∧ readServiceLayer layer = some (serviceInfo defs sv) := by
  unfold printService at h
  cases hinit : defs[sv.init]? with
  | none =>
    rw [hinit] at h
    cases h
  | some init =>
    rw [hinit] at h
    dsimp only at h
    obtain ⟨fields, -, rest⟩ := bind_eq_ok.mp h
    obtain ⟨closures, hclosures, heq⟩ := bind_eq_ok.mp rest
    cases heq
    refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    show (closures.mapM readServiceMethod).map (fun methods => (sv.name, init.name, methods)) = _
    rw [readServiceMethods_ok hclosures]
    simp only [serviceInfo, hinit, Option.map_some, Option.getD_some]

/-! ## What a block whose services print satisfies -/

/-- What `serviceFault` checks, when it finds no fault: distinct definition names in a block with
a service, no method of a service that the block does not declare, and no fault of one service. -/
theorem serviceFault_none {defs : List DefDecl} (h : serviceFault defs = none) :
    ((servicesOf defs).isEmpty = false → (defs.map (·.name)).Nodup) ∧
      (∀ d ∈ defs, strayMethod ((servicesOf defs).map (·.name)) d = false) ∧
      (servicesOf defs).findSome? (serviceFaultOf defs) = none := by
  unfold serviceFault at h
  split at h
  · cases h
  · rename_i hnames
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i hstray
        refine ⟨?_, ?_, h⟩
        · intro hne
          cases hn : decide ((defs.map (·.name)).Nodup) with
          | true => exact of_decide_eq_true hn
          | false => exact absurd (by rw [hne, hn]; rfl) hnames
        · intro d hd
          cases hs : strayMethod ((servicesOf defs).map (·.name)) d with
          | false => rfl
          | true => exact absurd (List.any_eq_true.mpr ⟨d, hd, hs⟩) hstray

/-- A service that prints has a name and a layer name that carry no layer path. -/
theorem serviceFaultOf_names {defs : List DefDecl} {sv : Service}
    (h : serviceFaultOf defs sv = none) :
    LayerTerm.readRefName sv.name = none ∧ LayerTerm.readRefName (sv.name ++ "Layer") = none := by
  unfold serviceFaultOf at h
  cases hinit : defs[sv.init]? with
  | none =>
    rw [hinit] at h
    cases h
  | some init =>
    rw [hinit] at h
    dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i hnames
          constructor
          · cases hr : LayerTerm.readRefName sv.name with
            | none => rfl
            | some _ =>
              exact absurd (by simp only [hr, Option.isSome_some, Bool.or_true, Bool.true_or]) hnames
          · cases hr : LayerTerm.readRefName (sv.name ++ "Layer") with
            | none => rfl
            | some _ =>
              exact absurd (by simp only [hr, Option.isSome_some, Bool.or_true]) hnames

/-- The printed constants of services that print, each plain, a service constant and free of a
layer path; their layers read back as the services' information. -/
theorem printServiceList_ok {sig : Signature Op} {defs : List DefDecl} :
    ∀ {services : List Service} {groups : List (List TypeScript.ConstDecl)},
      (∀ sv ∈ services, serviceFaultOf defs sv = none) →
      services.mapM (printService sig defs) = .ok groups →
      (∀ c ∈ groups.flatten, c.type = none ∧ c.exported = true ∧ isServiceConst c = true ∧
        LayerTerm.readRefName c.name = none) ∧
      groups.flatten.filterMap readServiceLayer = services.map (serviceInfo defs)
  | [], groups, _, h => by
    cases h
    exact ⟨(fun _ mem => nomatch mem), rfl⟩
  | sv :: rest, groups, faults, h => by
    rw [List.mapM_cons] at h
    obtain ⟨cs, hcs, tail⟩ := bind_eq_ok.mp h
    obtain ⟨gs, hgs, heq⟩ := bind_eq_ok.mp tail
    cases heq
    obtain ⟨key, layer, rfl, kt, ke, lt, le, ks, ls, kn, ln, kr, lr⟩ := printService_ok hcs
    obtain ⟨knames, lnames⟩ := serviceFaultOf_names (faults sv List.mem_cons_self)
    obtain ⟨hrest, hread⟩ :=
      printServiceList_ok (fun sv' h' => faults sv' (List.mem_cons_of_mem _ h')) hgs
    refine ⟨?_, ?_⟩
    · intro c mem
      rw [List.flatten_cons, List.mem_append] at mem
      rcases mem with mem | mem
      · rcases List.mem_cons.mp mem with rfl | mem
        · exact ⟨kt, ke, ks, by rw [kn]; exact knames⟩
        · rcases List.mem_cons.mp mem with rfl | mem
          · exact ⟨lt, le, ls, by rw [ln]; exact lnames⟩
          · cases mem
      · exact hrest c mem
    · rw [List.flatten_cons, List.filterMap_append, hread]
      simp only [List.filterMap_cons, kr, lr, List.filterMap_nil, List.map_cons]
      rfl

/-- **A block's printed services**: their constants are plain service constants free of a layer
path, and their layers read back as the services' information. -/
theorem printServices_ok {sig : Signature Op} {defs : List DefDecl}
    {svc : List TypeScript.ConstDecl} (h : printServices sig defs = .ok svc) :
    serviceFault defs = none ∧
      (∀ c ∈ svc, c.type = none ∧ c.exported = true ∧ isServiceConst c = true ∧
        LayerTerm.readRefName c.name = none) ∧
      svc.filterMap readServiceLayer = (servicesOf defs).map (serviceInfo defs) := by
  unfold printServices at h
  cases hf : serviceFault defs with
  | some why =>
    rw [hf] at h
    cases h
  | none =>
    rw [hf] at h
    dsimp only at h
    obtain ⟨groups, hgroups, heq⟩ := bind_eq_ok.mp h
    cases heq
    have faults := List.findSome?_eq_none_iff.mp (serviceFault_none hf).2.2
    exact ⟨rfl, printServiceList_ok faults hgroups⟩

/-! ## The roles come back -/

/-- The information of a block's services gives each definition its role, at a block whose
services print. A step of `readModule_printModule_defs`. -/
theorem roleOf_servicesOf {defs : List DefDecl} (hf : serviceFault defs = none) {d : DefDecl}
    (hd : d ∈ defs) : roleOf ((servicesOf defs).map (serviceInfo defs)) d.name = d.role := by
  obtain ⟨hnodup, hstray, -⟩ := serviceFault_none hf
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hd
  -- an initial program's information names the definition at its position
  have initNamed : ∀ e ∈ (servicesOf defs).map (serviceInfo defs), e.2.1 = d.name →
      d.role = .serviceInit e.1 := by
    intro e he hname
    obtain ⟨sv, hsv, rfl⟩ := List.mem_map.mp he
    obtain ⟨d', hd', hrole, -⟩ := mem_servicesOf.mp hsv
    have hne : (servicesOf defs).isEmpty = false := List.isEmpty_eq_false_iff.mpr
      (List.ne_nil_of_mem hsv)
    have hname' : d'.name = d.name := by
      simp only [serviceInfo, hd', Option.map_some, Option.getD_some] at hname
      exact hname
    have hidx := index_eq_of_name (hnodup hne) hd' hi hname'
    rw [hidx, hi] at hd'
    cases hd'
    exact hrole
  -- a method's information names the definition at its position
  have methodNamed : ∀ x ∈ (((servicesOf defs).map (serviceInfo defs)).flatMap fun sv =>
      sv.2.2.map fun m => (sv.1, m)), x.2.2.1 = d.name →
      d.role = .serviceMethod x.1 x.2.1 x.2.2.2 := by
    intro x hx hname
    obtain ⟨e, he, hxe⟩ := List.mem_flatMap.mp hx
    obtain ⟨sv, hsv, rfl⟩ := List.mem_map.mp he
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hxe
    obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
    obtain ⟨-, -, -, hmethods⟩ := mem_servicesOf.mp hsv
    rw [hmethods] at hy'
    obtain ⟨d'', hd'', hrole⟩ := mem_serviceMethods.mp hy'
    have hne : (servicesOf defs).isEmpty = false := List.isEmpty_eq_false_iff.mpr
      (List.ne_nil_of_mem hsv)
    have hname' : d''.name = d.name := by
      simp only [hd'', Option.map_some, Option.getD_some] at hname
      exact hname
    have hidx := index_eq_of_name (hnodup hne) hd'' hi hname'
    rw [hidx, hi] at hd''
    cases hd''
    exact hrole
  unfold roleOf
  cases hrole : d.role with
  | plain =>
    have hinit : ((servicesOf defs).map (serviceInfo defs)).find?
        (fun sv => decide (sv.2.1 = d.name)) = none := by
      rw [List.find?_eq_none]
      intro e he hdec
      have := initNamed e he (of_decide_eq_true hdec)
      rw [hrole] at this
      cases this
    have hmeth : (((servicesOf defs).map (serviceInfo defs)).flatMap fun sv =>
        sv.2.2.map fun m => (sv.1, m)).find? (fun x => decide (x.2.2.1 = d.name)) = none := by
      rw [List.find?_eq_none]
      intro x hx hdec
      have := methodNamed x hx (of_decide_eq_true hdec)
      rw [hrole] at this
      cases this
    rw [hinit]
    dsimp only
    rw [hmeth]
  | serviceInit s =>
    have hsv : (⟨s, i, serviceMethods s defs⟩ : Service) ∈ servicesOf defs :=
      mem_servicesOf.mpr ⟨d, hi, hrole, rfl⟩
    have hmem : serviceInfo defs ⟨s, i, serviceMethods s defs⟩ ∈
        (servicesOf defs).map (serviceInfo defs) := List.mem_map_of_mem hsv
    cases hfind : ((servicesOf defs).map (serviceInfo defs)).find?
        (fun sv => decide (sv.2.1 = d.name)) with
    | none =>
      have := List.find?_eq_none.mp hfind _ hmem
      exact absurd (decide_eq_true (by simp only [serviceInfo, hi, Option.map_some,
        Option.getD_some])) this
    | some e =>
      have he := List.mem_of_find?_eq_some hfind
      have hsome := List.find?_some hfind
      have hname := of_decide_eq_true hsome
      have := initNamed e he hname
      rw [hrole] at this
      cases this
      rfl
  | serviceMethod s m k =>
    have hinit : ((servicesOf defs).map (serviceInfo defs)).find?
        (fun sv => decide (sv.2.1 = d.name)) = none := by
      rw [List.find?_eq_none]
      intro e he hdec
      have := initNamed e he (of_decide_eq_true hdec)
      rw [hrole] at this
      cases this
    rw [hinit]
    dsimp only
    have hs : strayMethod ((servicesOf defs).map (·.name)) d = false := hstray d hd
    have hsname : s ∈ (servicesOf defs).map (·.name) := by
      unfold strayMethod at hs
      rw [hrole] at hs
      simp only [Bool.not_eq_false', List.contains_iff_mem] at hs
      exact hs
    obtain ⟨sv, hsv, hsvname⟩ := List.mem_map.mp hsname
    obtain ⟨-, -, -, hmethods⟩ := mem_servicesOf.mp hsv
    have hy : (m, i, k) ∈ sv.methods := by
      rw [hmethods, hsvname]
      exact mem_serviceMethods.mpr ⟨d, hi, hrole⟩
    have hmem : (s, (m, d.name, k)) ∈ (((servicesOf defs).map (serviceInfo defs)).flatMap fun sv =>
        sv.2.2.map fun m => (sv.1, m)) := by
      refine List.mem_flatMap.mpr ⟨serviceInfo defs sv, List.mem_map_of_mem hsv, ?_⟩
      refine List.mem_map.mpr ⟨(m, d.name, k), ?_, by rw [serviceInfo, hsvname]⟩
      refine List.mem_map.mpr ⟨(m, i, k), hy, ?_⟩
      simp only [hi, Option.map_some, Option.getD_some]
    cases hfind : (((servicesOf defs).map (serviceInfo defs)).flatMap fun sv =>
        sv.2.2.map fun m => (sv.1, m)).find? (fun x => decide (x.2.2.1 = d.name)) with
    | none =>
      exact absurd (decide_eq_true rfl) (List.find?_eq_none.mp hfind _ hmem)
    | some x =>
      have hx := List.mem_of_find?_eq_some hfind
      have hsome := List.find?_some hfind
      have hname := of_decide_eq_true hsome
      have := methodNamed x hx hname
      rw [hrole] at this
      obtain ⟨xs, xm, xd, xk⟩ := x
      cases this
      rfl

/-- **The definitions come back with their roles**: definitions read back with plain roles, then
given the roles of the block's services, are the block's definitions. A step of
`readModule_printModule_defs`. -/
theorem restoreRoles {defs : List DefDecl} (hf : serviceFault defs = none)
    {heads : List (DefDecl × TypeScript.Expr)}
    (hdefs : heads.map (·.1) = defs.map fun d => { d with role := .plain }) :
    (heads.map fun h => { h.1 with role := roleOf ((servicesOf defs).map (serviceInfo defs)) h.1.name })
      = defs := by
  have split : (heads.map fun h =>
      { h.1 with role := roleOf ((servicesOf defs).map (serviceInfo defs)) h.1.name }) =
      (heads.map (·.1)).map fun d =>
        { d with role := roleOf ((servicesOf defs).map (serviceInfo defs)) d.name } := by
    rw [List.map_map]
    rfl
  rw [split, hdefs, List.map_map]
  conv => rhs; rw [← List.map_id defs]
  apply List.map_congr_left
  intro d hd
  show { d with role := roleOf ((servicesOf defs).map (serviceInfo defs)) d.name } = d
  rw [roleOf_servicesOf hf hd]

end Effect4.Program
