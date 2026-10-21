import Effect4.Codegen.Print
import Effect4.Codegen.Surface
import Effect4.Laws.Codegen.Services
import Effect4.Api.Author
import Effect4.Program.Authoring.ApplicationService
import Test.Dogfood.Scenario.Todo.Data

/-!
# Probe: the service view is a reading of the roles; its fault check mixes two judgments

`servicesOf` reads a block's services off its definitions' roles, and `serviceFault` decides
whether they print (`src/Effect4/Codegen/Print.lean`). Two of the checks in `serviceFault` are
formation of the roles: an initial program at a unit request, methods with distinct names, each
method's request the state and its arguments, no method of an undeclared service. The others are
the TypeScript printer's names: a method name is a TypeScript identifier other than `__proto__`
(`plainMethodName`), a service's key and layer constants `S` and `SLayer` collide with no
definition and carry no layer path, and definitions have distinct names.

This probe writes the check once over a profile of names (`NameProfile`), shows that the printer's
check is that function at the TypeScript profile by `rfl`, and proves that the printer's check
implies the domain's (`serviceFaultIn_anyName`). It then reads the to-do's service, and keeps two
controls: a method named `delete` (the domain admits it, the printer refuses it), and a method whose
request is not the state and its arguments (both refuse it, at the method).
-/

set_option autoImplicit false

namespace Probe.Service

open Effect4 Effect4.Program Effect4.Codegen

/-- **The names a target accepts beside a block's services**, as data. -/
structure NameProfile where
  /-- a fault among the definitions' names, in a block with a service -/
  defNameFault : List DefDecl → Option String
  /-- the constants a service declares, which no two services may share -/
  serviceConsts : String → List String
  /-- a method name the target accepts -/
  method : String → Bool
  /-- whether a service's constants collide with the block's definitions or names -/
  collides : List DefDecl → String → Bool

/-- **The TypeScript printer's profile**: each field is the corresponding check of
`serviceFault`, written as it is written there. -/
def tsProfile : NameProfile where
  defNameFault defs := if (servicesOf defs).isEmpty then none else repeatOf (defs.map (·.name))
  serviceConsts s := [s, s ++ "Layer"]
  method := plainMethodName
  collides defs s := defs.any (·.name == s) || defs.any (·.name == s ++ "Layer") ||
    (LayerTerm.readRefName s).isSome || (LayerTerm.readRefName (s ++ "Layer")).isSome

/-- **The program domain's profile**: a service is named by its own name, and no name is a
target's business. -/
def anyName : NameProfile where
  defNameFault _ := none
  serviceConsts s := [s]
  method _ := true
  collides _ _ := false

/-- One service's fault under a profile: `serviceFaultOf` with its name checks read from the
profile. -/
def serviceFaultOfIn (p : NameProfile) (defs : List DefDecl) (sv : Service) : Option PrintRefusal :=
  match defs[sv.init]? with
  | none => some (.service sv.name)
  | some init =>
    if init.request ≠ .unit || !init.params.isEmpty then some (.service sv.name)
    else if !(sv.methods.map (·.1)).Nodup || sv.methods.isEmpty ||
        sv.methods.any (fun x => !p.method x.1) then some (.service sv.name)
    else if p.collides defs sv.name then
      some (.service sv.name)
    else sv.methods.findSome? fun (m, j, n) =>
      match defs[j]? with
      | some d =>
        if (methodArgs init.answer d n).isSome then none
        else some (.serviceMethod sv.name m)
      | none => some (.serviceMethod sv.name m)

/-- **A block's service fault under a profile**: `serviceFault` with its name checks read from
the profile. -/
def serviceFaultIn (p : NameProfile) (defs : List DefDecl) : Option PrintRefusal :=
  match p.defNameFault defs with
  | some n => some (.serviceName n)
  | none =>
  match repeatOf ((servicesOf defs).flatMap fun sv => p.serviceConsts sv.name) with
  | some n => some (.serviceName n)
  | none =>
  match strayOf ((servicesOf defs).map (·.name)) defs with
  | some why => some why
  | none => (servicesOf defs).findSome? (serviceFaultOfIn p defs)

/-- **The printer's check is the profiled check at TypeScript's names**, by definition: the
refactor changes no answer and no order. -/
theorem serviceFault_eq (defs : List DefDecl) : serviceFault defs = serviceFaultIn tsProfile defs :=
  rfl

/-- `repeatOf` finds nothing exactly on a list with no repeat. -/
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

/-- A service's own name is among the constants TypeScript declares for it. -/
theorem names_sublist (services : List Service) :
    (services.flatMap fun sv => anyName.serviceConsts sv.name).Sublist
      (services.flatMap fun sv => tsProfile.serviceConsts sv.name) := by
  induction services with
  | nil => exact List.Sublist.refl _
  | cons sv rest ih =>
    simp only [List.flatMap_cons]
    exact List.Sublist.append (List.Sublist.cons_cons _ (List.nil_sublist _)) ih

/-- One service: what the printer prints, the domain admits. -/
theorem serviceFaultOfIn_anyName {defs : List DefDecl} {sv : Service}
    (h : serviceFaultOfIn tsProfile defs sv = none) : serviceFaultOfIn anyName defs sv = none := by
  unfold serviceFaultOfIn at h ⊢
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hreq
      rw [if_neg hreq]
      split at h
      · cases h
      · rename_i hmethods
        have hany : sv.methods.any (fun x => !anyName.method x.1) = false := by
          rw [List.any_eq_false]
          intro x _ hx
          simp only [anyName, Bool.not_true, Bool.false_eq_true] at hx
        have hdomain : ¬ ((!(sv.methods.map (·.1)).Nodup || sv.methods.isEmpty ||
            sv.methods.any (fun x => !anyName.method x.1)) = true) := by
          rw [hany, Bool.or_false]
          intro hd
          exact hmethods (by rw [hd, Bool.true_or])
        rw [if_neg hdomain]
        split at h
        · cases h
        · exact h

/-- **What the printer prints, the domain admits**: the TypeScript profile's check implies the
program domain's. The converse fails at the names alone (the control below). -/
theorem serviceFaultIn_anyName {defs : List DefDecl} (h : serviceFaultIn tsProfile defs = none) :
    serviceFaultIn anyName defs = none := by
  unfold serviceFaultIn at h ⊢
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hts
      have hnames : repeatOf ((servicesOf defs).flatMap fun sv => anyName.serviceConsts sv.name) =
          none :=
        (repeatOf_eq_none_iff _).mpr
          ((names_sublist _).nodup ((repeatOf_eq_none_iff _).mp hts))
      simp only [anyName] at hnames ⊢
      rw [hnames]
      dsimp only
      split at h
      · cases h
      · rw [List.findSome?_eq_none_iff] at h ⊢
        intro sv hsv
        exact serviceFaultOfIn_anyName (h sv hsv)

/-- `mapM` in `Option` answers when every element does. -/
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
printer's entry reading (`entriesOf`, `src/Effect4/Codegen/Surface.lean`) answers every service. -/
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

/-- The object: a program with its signature (`probe-object.lean` holds its codec). -/
structure Object where
  app : SigApp
  program : Eff NativeOp

/-- **The object's service view**: the services its block's roles declare, when the roles are
formed; the refusal names the service, the method or the definition at fault. -/
def Object.services (o : Object) : Except PrintRefusal (List Service) :=
  match serviceFaultIn anyName o.program.defsOf with
  | some why => .error why
  | none => .ok (servicesOf o.program.defsOf)

/-! ## The to-do: a finite evaluation -/

/-- The to-do's service block, built as `Compiler.check` builds it. -/
def todoDefs : List DefDecl :=
  match Test.Dogfood.Scenario.Todo.application.serviceModule "TodoApp" with
  | .ok m => ((Api.Author.build m).toOption.map (·.program.defsOf)).getD []
  | .error _ => []

-- finite evaluation: one service, its initial program and four methods with their arities
#guard (servicesOf todoDefs).map (fun sv => (sv.name, sv.init, sv.methods)) =
  [("TodoApp", 0, [("add", 1, 1), ("list", 2, 0), ("complete", 3, 1), ("remove", 4, 1)])]
#guard serviceFault todoDefs = none
#guard serviceFaultIn anyName todoDefs = none
#guard (Object.services ⟨{}, .defs todoDefs .nil (.succeed (.lit .unit)) .nil⟩).toOption.map
  (·.length) = some 1

-- finite evaluation: the entries' argument types, read off each method's request
#guard ((servicesOf todoDefs).head?.bind (entriesOf todoDefs)).map
    (fun es => es.map fun e => (e.method, e.args)) =
  some [("add", [.string]), ("list", []), ("complete", [.nat]), ("remove", [.nat])]

/-- The to-do's block with its method `add` renamed. -/
def renamed (name : String) : List DefDecl :=
  todoDefs.map fun d => match d.role with
    | .serviceMethod s "add" n => { d with role := .serviceMethod s name n }
    | _ => d

-- control: `delete` is a reserved word of TypeScript; the roles are formed, and only the
-- printer's names refuse the block
#guard serviceFault (renamed "delete") = some (.service "TodoApp")
#guard serviceFaultIn anyName (renamed "delete") = none
#guard serviceFault (renamed "insert") = none

/-- The to-do's block with method `add`'s request replaced by `unit`. -/
def malformed : List DefDecl :=
  todoDefs.map fun d => match d.role with
    | .serviceMethod _ "add" _ => { d with request := .unit }
    | _ => d

-- control: a method whose request is not the state and its arguments is refused by both checks,
-- at the method
#guard serviceFault malformed = some (.serviceMethod "TodoApp" "add")
#guard serviceFaultIn anyName malformed = some (.serviceMethod "TodoApp" "add")

end Probe.Service
