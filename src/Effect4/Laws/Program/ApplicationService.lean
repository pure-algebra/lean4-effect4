import Effect4.Program.Authoring.ApplicationService
import Effect4.Laws.Program.Authoring

/-!
# Laws.Program.ApplicationService — the block of an application's service

Slice E1 of the emitted-services note (`docs/research/2026-10-13-emitted-services/README.md`,
"The laws it owes"; decisions row 378 (20)). The block that `Application.serviceDefs` builds
(`src/Effect4/Program/Authoring/ApplicationService.lean`) has three facts, each read off the
construction:

* **Each method declares its entry's checked type** (`serviceDefs_mem`, `methodDef_decl`).
  Every definition of the block is the initial program, or the method of an entry at a type `t`.
  That `t` is the checker's type of the entry's open program. The method's answer and error are
  `t`'s, and its requirement row is `t`'s less the rows' keys. This is the declaration half of the
  note's typing law; the build's block check (`Checker.checkModule`) is its other half.
* **A refusal of the block is an entry's, by its name** (`serviceDefs_error`).
* **A refused entry refuses the block** (`serviceDefs_of_refused`).

What they do not establish: that the block type-checks, or what a method means (the note's
meaning law, not stated here). Nothing here reads the TypeScript module.
-/

set_option autoImplicit false

namespace Effect4.Program.Authoring

open Effect4.Program

/-- A refusal of `mapM` over `Except` is the refusal of one element. A step of
`serviceDefs_error`. -/
theorem mapM_error_mem {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {r : ε}, l.mapM f = .error r → ∃ a ∈ l, f a = .error r := by
  intro l
  induction l with
  | nil => intro r h; cases h
  | cons a as ih =>
    intro r h
    simp only [List.mapM_cons] at h
    cases hfa : f a with
    | error r' =>
      rw [hfa] at h
      cases h
      exact ⟨a, List.mem_cons_self, hfa⟩
    | ok b =>
      rw [hfa] at h
      cases hrest : as.mapM f with
      | error r' =>
        rw [hrest] at h
        cases h
        obtain ⟨a', ha', hf⟩ := ih hrest
        exact ⟨a', List.mem_cons_of_mem _ ha', hf⟩
      | ok bs =>
        rw [hrest] at h
        cases h

/-- A successful `mapM` over `Except` succeeds at each element. A step of
`serviceDefs_of_refused`. -/
theorem mapM_ok_each {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {ys : List β}, l.mapM f = .ok ys → ∀ a ∈ l, ∃ b, f a = .ok b := by
  intro l
  induction l with
  | nil => intro ys _ a ha; cases ha
  | cons a as ih =>
    intro ys h a' ha'
    simp only [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_ok h
    obtain ⟨bs, hbs, _⟩ := bind_ok h
    rcases List.mem_cons.mp ha' with rfl | ha'
    · exact ⟨b, hb⟩
    · exact ih hbs a' ha'

namespace Application

/-- **The declaration of an entry's method**: the definition `<service>_<e>`, whose request is the
state and then the entry's parameters, whose answer and error are the entry's type `t`'s, whose
requirement row is `t`'s less the rows' keys, and whose role is method `e` of the service, at the
entry's arity. -/
theorem methodDef_decl (app : Application NativeOp) (service : String)
    (e : Application.Entry NativeOp) (t : EffTy) :
    (app.methodDef service e t).decl =
      { name := service ++ "_" ++ e.name,
        request := requestTy (app.stateTy :: e.params.map (·.2)),
        answer := t.answer, error := t.error,
        requires := (Effect4.Row.diff t.requires app.contextKeys).elems,
        role := .serviceMethod service e.name e.params.length } := rfl

/-- **Each method declares its entry's checked type** (decisions row 378 (20)): every definition
of a built block is the service's initial program, or the method of an entry at the checker's type
of the entry's open program (`entryTy`), whose declaration `methodDef_decl` gives. -/
theorem serviceDefs_mem {app : Application NativeOp} {service : String}
    {defs : List (DefSrc NativeOp)} (h : app.serviceDefs service = .ok defs)
    {d : DefSrc NativeOp} (hd : d ∈ defs) :
    d = app.contextDef service ∨
      ∃ e ∈ app.entries, ∃ t, app.entryTy e = .ok t ∧ d = app.methodDef service e t := by
  unfold serviceDefs at h
  obtain ⟨methods, hm, h⟩ := bind_ok h
  cases h
  rcases List.mem_cons.mp hd with rfl | hd
  · exact .inl rfl
  · obtain ⟨e, he, hf⟩ := mapM_ok_mem hm d hd
    obtain ⟨t, ht, hf⟩ := bind_ok hf
    cases hf
    exact .inr ⟨e, he, t, ht, rfl⟩

/-- An entry's refusal names the entry: the scope reader's refusal of its open program, or the
checker's. A step of `serviceDefs_error`. -/
theorem entryTy_error {app : Application NativeOp} {e : Application.Entry NativeOp}
    {r : ServiceRefusal} (h : app.entryTy e = .error r) :
    (∃ s, r = .scope e.name s) ∨ ∃ s, r = .typing e.name s := by
  unfold entryTy at h
  split at h
  · rename_i s _
    cases h
    exact .inl ⟨s, rfl⟩
  · split at h
    · rename_i s _
      cases h
      exact .inr ⟨s, rfl⟩
    · cases h

/-- **A refusal of the block is an entry's, by its name** (decisions row 378 (20)): the block is
refused only at an entry of the application, with that entry's refusal, the scope reader's or
the checker's. -/
theorem serviceDefs_error {app : Application NativeOp} {service : String} {r : ServiceRefusal}
    (h : app.serviceDefs service = .error r) :
    ∃ e ∈ app.entries, app.entryTy e = .error r ∧
      ((∃ s, r = .scope e.name s) ∨ ∃ s, r = .typing e.name s) := by
  unfold serviceDefs at h
  cases hm : app.entries.mapM (fun e => do
      let t ← app.entryTy e
      pure (app.methodDef service e t)) with
  | ok methods =>
    rw [hm] at h
    cases h
  | error r' =>
    rw [hm] at h
    cases h
    obtain ⟨e, he, hf⟩ := mapM_error_mem hm
    cases ht : app.entryTy e with
    | ok t =>
      rw [ht] at hf
      cases hf
    | error s =>
      rw [ht] at hf
      cases hf
      exact ⟨e, he, ht, entryTy_error ht⟩

/-- **A refused entry refuses the block** (decisions row 378 (20)): an entry that the scope
reader or the checker refuses leaves the application with no service block. -/
theorem serviceDefs_of_refused {app : Application NativeOp} {service : String}
    {e : Application.Entry NativeOp} (he : e ∈ app.entries) {r : ServiceRefusal}
    (hr : app.entryTy e = .error r) : ∃ r', app.serviceDefs service = .error r' := by
  cases h : app.serviceDefs service with
  | error r' => exact ⟨r', rfl⟩
  | ok defs =>
    unfold serviceDefs at h
    obtain ⟨methods, hm, _⟩ := bind_ok h
    obtain ⟨d, hd⟩ := mapM_ok_each hm e he
    obtain ⟨t, ht, _⟩ := bind_ok hd
    rw [hr] at ht
    cases ht

end Application

end Effect4.Program.Authoring
