import Effect4.Laws.Codegen.ReadLeaf
import Effect4.Codegen.Surface
import Effect4.Laws.Auto.Semantics

/-!
# Codegen.Services — a block's services read back (decisions rows 338 and 339, slice CO-6b)

A block's roles declare its services (`DefRole`), and the printer prints each as its key and its
layer after the definitions (`printServices`, `src/Effect4/Codegen/Print.lean`). The reader gives
the roles back from the layers (`roleOf`, `src/Effect4/Codegen/Read.lean`). This module proves the
three facts that the round trip of a block uses (`readModuleWith_printModuleWith_defs`,
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

open Effect4.Laws.Auto (bind_eq_ok)

namespace Effect4.Program

open Effect4.Codegen (Entry entriesOf)

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

/-- The names of what `mapM` builds, when each built value is named by the first component of its
input. A step of `readServiceMethods_ok`: a closure's parameters are named `a1` to `an`. -/
theorem names_of_mapM {f : String × Ty → Except PrintRefusal TypeScript.Parameter}
    (hf : ∀ p q, f p = .ok q → q.name = p.1) :
    ∀ {l : List (String × Ty)} {params : List TypeScript.Parameter},
      l.mapM f = .ok params → params.map (·.name) = l.map (·.1)
  | [], params, h => by
    cases h
    rfl
  | p :: l, params, h => by
    rw [List.mapM_cons] at h
    obtain ⟨q, hq, rest⟩ := bind_eq_ok.mp h
    obtain ⟨qs, hqs, heq⟩ := bind_eq_ok.mp rest
    cases heq
    simp only [List.map_cons, hf p q hq, names_of_mapM hf hqs]

/-- The tuple of a nonempty list of arguments is recognized as that tuple. A step of
`readServiceMethods_ok`. -/
theorem isArgTuple_argTuple : ∀ {args : List String}, args ≠ [] → isArgTuple args (argTuple args) = true
  | [a], _ => decide_eq_true rfl
  | a :: b :: rest, _ => by
    show (decide (a = a) && isArgTuple (b :: rest) (argTuple (b :: rest))) = true
    rw [decide_eq_true rfl, isArgTuple_argTuple (List.cons_ne_nil b rest)]
    rfl

/-- A method's request is recognized as the request of its arguments. A step of
`readServiceMethods_ok`. -/
theorem isMethodRequest_methodRequest : ∀ (args : List String),
    isMethodRequest args (methodRequest args) = true
  | [] => by
    show decide (Var.name 0 = Var.name 0) = true
    exact decide_eq_true rfl
  | a :: rest => by
    show (decide (Var.name 0 = Var.name 0) && isArgTuple (a :: rest) (argTuple (a :: rest))) = true
    rw [decide_eq_true rfl, isArgTuple_argTuple (List.cons_ne_nil a rest)]
    rfl

/-- The programs that a method's closure passes on read back as their names. A step of
`readServiceMethods_ok` (slice HO-5). -/
theorem mapM_passedName : ∀ (qs : List ParamDecl),
    (qs.map fun q => TypeScript.Expr.ident q.name).mapM passedName = some (qs.map (·.name))
  | [] => rfl
  | q :: qs => by
    rw [List.map_cons, List.mapM_cons, mapM_passedName qs]
    rfl

/-- The closures of a printed layer read back as its methods' information: the arity is the
closure's parameters less the programs that it passes on (slice HO-5). -/
theorem readServiceMethods_ok {sig : Signature Op} {service : String} {defs : List DefDecl}
    {init : DefDecl} :
    ∀ {methods : List (String × Nat × Nat)} {closures : List (String × TypeScript.Expr)},
      methods.mapM (methodClosure sig service init defs) = .ok closures →
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
        obtain ⟨params, hparams, rest'⟩ := bind_eq_ok.mp hc
        obtain ⟨fns, hfns, heq⟩ := bind_eq_ok.mp rest'
        cases heq
        have hargs : (argNames n).length = n := by
          simp only [argNames, List.length_map, List.length_range]
        have hlen : params.length = n := by
          rw [length_of_mapM_ok hparams, List.length_zip, length_methodArgs htys, hargs,
            Nat.min_self]
        have hnames : params.map (·.name) = argNames n := by
          rw [names_of_mapM (fun p q hpq => by
              obtain ⟨r, -, heq⟩ := bind_eq_ok.mp hpq
              cases heq
              rfl) hparams,
            List.map_fst_zip (by rw [hargs, length_methodArgs htys]; exact Nat.le_refl n)]
        have hfnslen : fns.length = d.params.length := length_of_mapM_ok hfns
        have hfst : (d.params.zip fns).map Prod.fst = d.params :=
          List.map_fst_zip (by rw [hfnslen]; exact Nat.le_refl _)
        have hpassed : ((d.params.zip fns).map fun q =>
            ({ name := q.1.name, type := some q.2 } : TypeScript.Parameter)).map (·.name) =
            d.params.map (·.name) := by
          rw [List.map_map]
          conv => rhs; rw [← hfst]
          rw [List.map_map]
          rfl
        have hcount : (params ++ (d.params.zip fns).map fun q =>
            ({ name := q.1.name, type := some q.2 } : TypeScript.Parameter)).length -
            (d.params.map (·.name)).length = n := by
          rw [List.length_append, List.length_map, List.length_zip, hfnslen, Nat.min_self, hlen,
            List.length_map, Nat.add_sub_cancel]
        have hread : readServiceMethod
            (m, .lambda (params ++ (d.params.zip fns).map fun q =>
                ({ name := q.1.name, type := some q.2 } : TypeScript.Parameter))
              (.call (.ident d.name) (methodRequest (argNames n) :: d.params.map fun q =>
                .ident q.name)) none) =
            some (m, d.name, n) := by
          simp only [readServiceMethod, mapM_passedName, hcount, List.map_append, hnames, hpassed,
            isMethodRequest_methodRequest, decide_true, Bool.and_self, ↓reduceIte]
        rw [List.mapM_cons, readServiceMethods_ok hcs, hread]
        simp only [hd, Option.map_some, Option.getD_some, List.map_cons]
        rfl

/-- **A printed service**: its key and its layer, both plain service constants named for the
service; the key is the service's key, and the layer reads back as the service's information. -/
theorem printService_ok {sig : Signature Op} {defs : List DefDecl} {sv : Service}
    {cs : List TypeScript.ConstDecl} (h : printService sig defs sv = .ok cs) :
    ∃ key layer, cs = [key, layer] ∧ key.type = none ∧ key.exported = true ∧
      layer.type = none ∧ layer.exported = true ∧ isServiceConst key = true ∧
      isServiceConst layer = true ∧ key.name = sv.name ∧ layer.name = sv.name ++ "Layer" ∧
      isServiceKey sv.name key = true ∧ readServiceLayer layer = some (serviceInfo defs sv) := by
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
    refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · show (decide (sv.name = sv.name) && (decide (sv.name = sv.name) &&
        decide (sv.name = sv.name))) = true
      rw [decide_eq_true rfl]
      rfl
    · show (if decide ((({ name := Var.name 0 } : TypeScript.Parameter)) = { name := Var.name 0 })
        then (closures.mapM readServiceMethod).map (fun methods => (sv.name, init.name, methods))
        else none) = _
      rw [decide_eq_true rfl, if_pos rfl, readServiceMethods_ok hclosures]
      simp only [serviceInfo, hinit, Option.map_some, Option.getD_some]

/-! ## What a block whose services print satisfies -/

/-- A list in which no name repeats a later one has no duplicate: what `repeatOf` checks when it
finds no repeat. A step of `serviceFault_none`, its consumer. -/
theorem nodup_of_repeatOf : ∀ {names : List String}, repeatOf names = none → names.Nodup
  | [], _ => List.nodup_nil
  | n :: rest, h => by
    simp only [repeatOf] at h
    cases hc : rest.contains n with
    | true =>
      rw [hc, if_pos rfl] at h
      cases h
    | false =>
      rw [hc, if_neg Bool.false_ne_true] at h
      exact List.nodup_cons.mpr
        ⟨fun hm => Bool.false_ne_true (hc.symm.trans (List.contains_iff_mem.mpr hm)),
          nodup_of_repeatOf h⟩

/-- No definition is a method of a service the block does not declare when `strayOf` finds none.
A step of `serviceFault_none`, its consumer. -/
theorem strayMethod_of_strayOf {names : List String} :
    ∀ {defs : List DefDecl}, strayOf names defs = none → ∀ d ∈ defs, strayMethod names d = false
  | [], _, _, hd => nomatch hd
  | d :: ds, h, e, he => by
    simp only [strayOf] at h
    cases hr : d.role with
    | plain =>
      rw [hr] at h
      dsimp only at h
      rcases List.mem_cons.mp he with heq | he
      · rw [heq]
        simp only [strayMethod, hr]
      · exact strayMethod_of_strayOf h e he
    | serviceInit s =>
      rw [hr] at h
      dsimp only at h
      rcases List.mem_cons.mp he with heq | he
      · rw [heq]
        simp only [strayMethod, hr]
      · exact strayMethod_of_strayOf h e he
    | serviceMethod s m k =>
      rw [hr] at h
      dsimp only at h
      cases hc : names.contains s with
      | false =>
        rw [hc, if_neg Bool.false_ne_true] at h
        cases h
      | true =>
        rw [hc, if_pos rfl] at h
        rcases List.mem_cons.mp he with heq | he
        · rw [heq]
          simp only [strayMethod, hr, hc, Bool.not_true]
        · exact strayMethod_of_strayOf h e he

/-- What `serviceFault` checks, when it finds no fault: distinct definition names in a block with
a service, no method of a service that the block does not declare, and no fault of one service. -/
theorem serviceFault_none {defs : List DefDecl} (h : serviceFault defs = none) :
    ((servicesOf defs).isEmpty = false → (defs.map (·.name)).Nodup) ∧
      (∀ d ∈ defs, strayMethod ((servicesOf defs).map (·.name)) d = false) ∧
      (servicesOf defs).findSome? (serviceFaultOf defs) = none := by
  unfold serviceFault serviceFaultIn tsProfile at h
  split at h
  · cases h
  · rename_i hnames
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i hstray
        refine ⟨fun hne => ?_, strayMethod_of_strayOf hstray, h⟩
        dsimp only at hnames
        rw [hne, if_neg Bool.false_ne_true] at hnames
        exact nodup_of_repeatOf hnames

/-- A service that prints has a name and a layer name that carry no layer path. -/
theorem serviceFaultOf_names {defs : List DefDecl} {sv : Service}
    (h : serviceFaultOf defs sv = none) :
    LayerTerm.readRefName sv.name = none ∧ LayerTerm.readRefName (sv.name ++ "Layer") = none := by
  unfold serviceFaultOf serviceFaultOfIn tsProfile at h
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
      readServices groups.flatten = some (services.map (serviceInfo defs))
  | [], groups, _, h => by
    cases h
    exact ⟨(fun _ mem => nomatch mem), rfl⟩
  | sv :: rest, groups, faults, h => by
    rw [List.mapM_cons] at h
    obtain ⟨cs, hcs, tail⟩ := bind_eq_ok.mp h
    obtain ⟨gs, hgs, heq⟩ := bind_eq_ok.mp tail
    cases heq
    obtain ⟨key, layer, rfl, kt, ke, lt, le, ks, ls, kn, ln, kk, lr⟩ := printService_ok hcs
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
    · show readServices (key :: layer :: gs.flatten) = _
      have hkey : isServiceKey (serviceInfo defs sv).1 key = true := kk
      have hlayer : decide (layer.name = (serviceInfo defs sv).1 ++ "Layer") = true :=
        decide_eq_true ln
      simp only [readServices, lr, Option.bind_eq_bind, Option.bind_some, hkey, hlayer,
        Bool.and_self, ↓reduceIte, hread, List.map_cons]
      rfl

/-- **A block's printed services**: their constants are plain service constants free of a layer
path, and their layers read back as the services' information. -/
theorem printServices_ok {sig : Signature Op} {defs : List DefDecl}
    {svc : List TypeScript.ConstDecl} (h : printServices sig defs = .ok svc) :
    serviceFault defs = none ∧
      (∀ c ∈ svc, c.type = none ∧ c.exported = true ∧ isServiceConst c = true ∧
        LayerTerm.readRefName c.name = none) ∧
      readServices svc = some ((servicesOf defs).map (serviceInfo defs)) := by
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
services print. A step of `readModuleWith_printModuleWith_defs`. -/
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
`readModuleWith_printModuleWith_defs`. -/
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

/-! ## The domain service view

The TypeScript profile's check is the domain's role check and TypeScript's naming conditions
(`serviceFaultIn_tsProfile_iff`). The connector and helpers serve `service-view-printed`; the
entry-reading helpers serve `service-view`. Their placement precedes
these proofs in `docs/research/2026-10-21-program-domain-landing/README.md` at `4d0b06374`.
-/

/-- **The printer's check is the profiled check at TypeScript's names**, by definition: the
refactor changes no answer and no order. -/
theorem serviceFault_eq (defs : List DefDecl) : serviceFault defs = serviceFaultIn tsProfile defs :=
  rfl

/-- `repeatOf` finds nothing exactly on a list with no repeat.
A step of `serviceFaultIn_tsProfile_iff`, the consumer for `service-view-printed`. -/
theorem repeatOf_eq_none_iff : ∀ (names : List String), repeatOf names = none ↔ names.Nodup
  | [] => ⟨fun _ => List.nodup_nil, fun _ => rfl⟩
  | n :: rest => by
    constructor
    · exact nodup_of_repeatOf
    · intro h
      obtain ⟨hn, hrest⟩ := List.nodup_cons.mp h
      have hc : rest.contains n = false := by
        cases hc : rest.contains n with
        | false => rfl
        | true => exact absurd (List.contains_iff_mem.mp hc) hn
      simp only [repeatOf, hc, Bool.false_eq_true, ↓reduceIte]
      exact (repeatOf_eq_none_iff rest).mpr hrest

/-- A service's own name is among the constants TypeScript declares for it.
A step of `serviceFaultIn_tsProfile_iff`, the consumer for `service-view-printed`. -/
theorem names_sublist (services : List Service) :
    (services.flatMap fun sv => anyName.serviceConsts sv.name).Sublist
      (services.flatMap fun sv => tsProfile.serviceConsts sv.name) := by
  induction services with
  | nil => exact List.Sublist.refl _
  | cons sv rest ih =>
    simp only [List.flatMap_cons]
    exact List.Sublist.append (List.Sublist.cons_cons _ (List.nil_sublist _)) ih

/-- **TypeScript's naming conditions** on a block's services, beside role formation: no
definition name repeats in a block with a service, no service constant repeats (a key or a
layer), every method name is a plain key, and no service's constants collide with the block. -/
def tsNames (defs : List DefDecl) : Prop :=
  tsProfile.defNameFault defs = none ∧
  repeatOf ((servicesOf defs).flatMap fun sv => tsProfile.serviceConsts sv.name) = none ∧
  ∀ sv ∈ servicesOf defs,
    sv.methods.any (fun x => !plainMethodName x.1) = false ∧
    tsProfile.collides defs sv.name = false

/-- The domain's profile refuses no method name.
A step of `serviceFaultIn_tsProfile_iff`, the consumer for `service-view-printed`. -/
theorem any_not_anyName (methods : List (String × Nat × Nat)) :
    methods.any (fun x => !anyName.method x.1) = false := by
  rw [List.any_eq_false]
  intro x _ hx
  simp only [anyName, Bool.not_true, Bool.false_eq_true] at hx

/-- One service: the printer's check is formation and the two naming conditions.
A step of `serviceFaultIn_tsProfile_iff`, the consumer for `service-view-printed`. -/
theorem serviceFaultOfIn_tsProfile_iff (defs : List DefDecl) (sv : Service) :
    serviceFaultOfIn tsProfile defs sv = none ↔
      serviceFaultOfIn anyName defs sv = none ∧
        sv.methods.any (fun x => !plainMethodName x.1) = false ∧
        tsProfile.collides defs sv.name = false := by
  unfold serviceFaultOfIn
  cases hinit : defs[sv.init]? with
  | none => simp
  | some init =>
    dsimp only
    cases hreq : (init.request ≠ .unit || !init.params.isEmpty) with
    | true => simp
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [any_not_anyName]
      show _ ↔ (if (!(sv.methods.map (·.1)).Nodup || sv.methods.isEmpty || false) = true then _
        else if false = true then _ else _) = none ∧ _
      simp only [Bool.or_false, Bool.false_eq_true, ↓reduceIte]
      cases hshape : (!(sv.methods.map (·.1)).Nodup || sv.methods.isEmpty) with
      | true => simp
      | false =>
        simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        rw [show tsProfile.method = plainMethodName from rfl]
        cases hplain : sv.methods.any (fun x => !plainMethodName x.1) with
        | true => simp
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases hcoll : tsProfile.collides defs sv.name with
          | true => simp
          | false => simp

/-- **The printer's check is formation and naming**: the TypeScript profile's check succeeds
exactly when the program domain's does and TypeScript's naming conditions hold (`tsNames`). The
order the printer reports its refusals in is no part of the claim.

Placement: concept `exact-codecs`, compatibility claim `service-view-printed`, requirement R8.
The consumers are `Object.services`, through the printer's compatibility with domain role
formation, and the controls of `Test/Codegen/ProgramServices.lean`.
This establishes no target execution, method meaning or program admission. -/
@[semantics "exact-codecs" (requirement := R8)]
theorem serviceFaultIn_tsProfile_iff (defs : List DefDecl) :
    serviceFaultIn tsProfile defs = none ↔ serviceFaultIn anyName defs = none ∧ tsNames defs := by
  unfold serviceFaultIn tsNames
  cases hdef : tsProfile.defNameFault defs with
  | some n => simp
  | none =>
    dsimp only
    show _ ↔ (match (none : Option String) with
      | some n => some (PrintRefusal.serviceName n)
      | none => match repeatOf ((servicesOf defs).flatMap fun sv => anyName.serviceConsts sv.name) with
        | some n => some (.serviceName n)
        | none => match strayOf ((servicesOf defs).map (·.name)) defs with
          | some why => some why
          | none => (servicesOf defs).findSome? (serviceFaultOfIn anyName defs)) = none ∧ _
    dsimp only
    cases hts : repeatOf ((servicesOf defs).flatMap fun sv => tsProfile.serviceConsts sv.name) with
    | some n => simp
    | none =>
      dsimp only
      have hdom : repeatOf ((servicesOf defs).flatMap fun sv => anyName.serviceConsts sv.name) =
          none :=
        (repeatOf_eq_none_iff _).mpr ((names_sublist _).nodup ((repeatOf_eq_none_iff _).mp hts))
      rw [hdom]
      dsimp only
      cases hstray : strayOf ((servicesOf defs).map (·.name)) defs with
      | some why => simp
      | none =>
        dsimp only
        simp only [List.findSome?_eq_none_iff, true_and]
        constructor
        · intro h
          refine ⟨fun sv hsv => ((serviceFaultOfIn_tsProfile_iff defs sv).mp (h sv hsv)).1,
            fun sv hsv => ((serviceFaultOfIn_tsProfile_iff defs sv).mp (h sv hsv)).2⟩
        · rintro ⟨hform, hnames⟩ sv hsv
          exact (serviceFaultOfIn_tsProfile_iff defs sv).mpr ⟨hform sv hsv, hnames sv hsv⟩

/-- What the printer prints, the domain admits: the forward half of `serviceFaultIn_tsProfile_iff`.
Consumers: the readers of `Test/Codegen/ProgramServices.lean`. -/
theorem serviceFaultIn_anyName {defs : List DefDecl} (h : serviceFaultIn tsProfile defs = none) :
    serviceFaultIn anyName defs = none :=
  ((serviceFaultIn_tsProfile_iff defs).mp h).1

/-- `mapM` in `Option` answers when every element does.
A step of `entriesOf_isSome`, the consumer for `service-view`. -/
theorem mapM_isSome {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, (f x).isSome = true) → (l.mapM f).isSome = true
  | [], _ => rfl
  | x :: xs, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h x List.mem_cons_self)
    obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp
      (mapM_isSome fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [List.mapM_cons, hb, hbs]
    rfl

/-- **A formed block's methods all have their argument types**: under the domain's check, the
printer's entry reading (`entriesOf`, `src/Effect4/Codegen/Surface.lean`) answers every service.

Placement: concept `exact-codecs`, adequacy claim `service-view`, requirement R8.
The hypotheses are domain service-check success and membership in the block's service view.
The consumers are service entry readers and the program-domain object view.
This establishes no program admission, method meaning, target execution or host behavior. -/
theorem entriesOf_isSome {defs : List DefDecl} (h : serviceFaultIn anyName defs = none)
    {sv : Service} (hsv : sv ∈ servicesOf defs) : (entriesOf defs sv).isSome = true := by
  unfold serviceFaultIn at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · have hof := (List.findSome?_eq_none_iff.mp h) sv hsv
        unfold serviceFaultOfIn at hof
        split at hof
        · cases hof
        · rename_i init hinit
          split at hof
          · cases hof
          · split at hof
            · cases hof
            · split at hof
              · cases hof
              · have hall := List.findSome?_eq_none_iff.mp hof
                unfold entriesOf
                simp only [hinit]
                apply mapM_isSome
                intro x hx
                obtain ⟨m, j, n⟩ := x
                have hm := hall (m, j, n) hx
                dsimp only at hm ⊢
                split at hm
                · rename_i d hd
                  split at hm
                  · rename_i hargs
                    obtain ⟨args, hargs'⟩ := Option.isSome_iff_exists.mp hargs
                    simp only [hd]
                    change (methodArgs init.answer d n >>= fun args =>
                      pure ({ method := m, args, definition := d } : Entry)).isSome = true
                    rw [hargs']
                    rfl
                  · cases hm
                · cases hm

end Effect4.Program
