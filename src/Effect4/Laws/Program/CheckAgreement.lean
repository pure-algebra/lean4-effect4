import Effect4.Program.Check
import Effect4.Laws.Program.Typing.Restrict
import Effect4.Laws.Program.Typing.Rebase
import Effect4.Laws.Auto.Obligations
/-!
Placement for the V1 checking connectors:
Concept: initial-algebras-folds; checker-base-natural and source-annotation-agrees, R14.
Question: exact checker decomposition and signature-extension compatibility.
Reach: all module keys for combine_deps; positive part answers for run_part_extends.
Exclusions: program admission, negative extension hits, progress, and native execution.
Consumer: Checked.ask_value, SourceSession.feed, and Check.extension.
`combine_deps` is proved from the definitions: the module's joined parts are the module check's
answer and its table, part by part (`joinModule_deps`). No core constructor depends on it.
-/
set_option autoImplicit false
namespace Effect4.Program.Check
open Effect4 Effect4.Program Conform.Effect4.Typing Internal
theorem run_placed (d : SigData) (env : TyEnv) (q : NativeEff) (base : List Nat) :
    place base (run (.part d env q)) =
      ⟨(Annotate.check d.signature env base q).2,
        (Annotate.check d.signature env base q).1⟩ := by
  simp only [place, run, Annotate.check_eq]
  have ht := tableAt_rebase d.signature (some (.env env)) (.eff q) base []
  have hr := Checker.check_rebase d.signature base env [] q
  simp only [List.append_nil] at ht hr
  exact congr (congrArg Verdict.mk hr.symm) ht.symm

theorem run_part_extends {a b : SigData} (env : TyEnv) (q : NativeEff) (t : EffTy)
    (he : a.extendsB b = true) (hp : (run (.part a env q)).result = .ok t) :
    run (.part a env q) = run (.part b env q) := by
  have hc : Checker.check a.signature env [] q = .ok t := by
    simpa only [run, Annotate.check_eq] using hp
  have support := hasTy_sigProgram (check_sound a.signature q env [] t hc)
  have same := Annotate.check_restrict (SigData.extends_of_extendsB he) support env []
  exact (congrArg (fun out : List Table.Entry × Except TypeRefusal EffTy =>
    (⟨out.2, out.1⟩ : Verdict)) same).symm


/-! ## The module's parts joined are the module check

`deps` names one part check for each body with a declaration, one for the main program, and one
for a nonempty spine of module layers. `joinModule` joins their verdicts in that order. Each
statement below is a step of the claim `checker-combine-deps`, and names its consumer, up to
`combine_deps`. -/

/-- **The bodies' verdicts joined are `Table.bodies` and `Checker.checkBodies`**, in the spine's
order, and the verdicts after them are left over. A step of `checker-combine-deps`. Its consumer
is `joinModule_deps`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem joinBodies_deps (app : SigApp) (holes : RowTable) (allDecls : List DefDecl) :
    ∀ (bodies : Effs NativeOp) (decls : List DefDecl) (index : Nat) (base : List Nat)
      (rest : List Verdict),
    joinBodies decls bodies base
        ((bodyDeps app holes allDecls decls bodies index base).map (fun d => run d.input) ++ rest) =
      some (Table.bodies ((app.withHoles holes).signature.withDefs allDecls) decls bodies base,
        Checker.checkBodies ((app.withHoles holes).signature.withDefs allDecls) base decls bodies,
        rest)
  | .nil, decls, index, base, rest => by
    cases decls <;> rfl
  | .cons b bs, [], index, base, rest => by
    have ih := joinBodies_deps app holes allDecls bs [] index (base ++ [1]) rest
    have h0 : bodyDeps app holes allDecls [] bs index (base ++ [1]) = [] := by cases bs <;> rfl
    rw [h0, List.map_nil, List.nil_append] at ih
    show joinBodies [] (.cons b bs) base rest = _
    simp only [joinBodies, ih]
    rfl
  | .cons b bs, d :: ds, index, base, rest => by
    have ih := joinBodies_deps app holes allDecls bs ds (index + 1) (base ++ [1]) rest
    show joinBodies (d :: ds) (.cons b bs) base
      (run (.part ⟨app, holes, .body allDecls d.params⟩ [d.request.normalize] b) ::
        ((bodyDeps app holes allDecls ds bs (index + 1) (base ++ [1])).map (fun d => run d.input) ++
          rest)) = _
    have hr : (Annotate.check (SigData.signature ⟨app, holes, .body allDecls d.params⟩)
        [d.request.normalize] (base ++ [0]) b).2 =
        Checker.check (((app.withHoles holes).signature.withDefs allDecls).withParams d.params)
          [d.request.normalize] (base ++ [0]) b := by
      rw [Annotate.check_eq]
      rfl
    simp only [joinBodies, ih, run_placed, hr]
    rfl

/-- A nonempty list of layer signatures merges. A step of `checker-combine-deps`. Its consumer
is `layers_join`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem mergeNonempty_cons_isSome (l : LayerTy) :
    ∀ ls : List LayerTy, (LayerTy.mergeNonempty (l :: ls)).isSome = true
  | [] => rfl
  | m :: rest => by
    have ih := mergeNonempty_cons_isSome m rest
    show ((LayerTy.mergeNonempty (m :: rest)).map l.merge).isSome = true
    rw [Option.isSome_map]
    exact ih

/-- A refusal placed below the module layers' part, read back at the block's child `2`, is the
refusal placed below `2`. A step of `checker-combine-deps`. Its consumer is
`layerEntry_rebase`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem mapError_layer_rebase {α : Type} (x : Except TypeRefusal α) :
    (x.mapError (TypeRefusal.rebase [0, 0])).mapError layerRefusal =
      x.mapError (TypeRefusal.rebase [2]) := by
  cases x <;> rfl

/-- An entry of the layers' table placed below the module layers' part, read back at the
block's child `2`, is the entry placed below `2`. A step of `checker-combine-deps`. Its consumer
is `layers_join`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem layerEntry_rebase (e : Table.Entry) :
    (match (Table.Entry.rebase [0, 0] e).path with
      | 0 :: 0 :: rest => some (⟨2 :: rest, (Table.Entry.rebase [0, 0] e).env,
          (Table.Entry.rebase [0, 0] e).result.map fun r => r.mapError layerRefusal⟩ : Table.Entry)
      | _ => none) = some (Table.Entry.rebase [2] e) := by
  obtain ⟨path, env, result⟩ := e
  cases result with
  | none => rfl
  | some r =>
    show some (⟨2 :: path, env, some ((r.mapError (TypeRefusal.rebase [0, 0])).mapError
      layerRefusal)⟩ : Table.Entry) =
      some ⟨2 :: path, env, some (r.mapError (TypeRefusal.rebase [2]))⟩
    rw [mapError_layer_rebase]

/-- A `filterMap` whose function answers every element is a `map`. A step of
`checker-combine-deps`. Its consumer is `layers_join`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem filterMap_eq_map_of {α β : Type} {f : α → Option β} {g : α → β}
    (h : ∀ a, f a = some (g a)) : ∀ l : List α, l.filterMap f = l.map g
  | [] => rfl
  | a :: l => by
    rw [List.filterMap_cons_some (h a), List.map_cons, filterMap_eq_map_of h l]

/-- An answer bound by `Except.ok` is its continuation at the value. A step of
`checker-combine-deps`. Its consumer is `layers_join`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

/-- A list of layers that checks answers one signature for each layer, so at least one. A step
of `checker-combine-deps`. Its consumer is `layers_join`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem checkLayers_cons_ok {sig : Signature NativeOp} {p : List Nat} {h : LayerTerm NativeOp}
    {t : LayerTerms NativeOp} {ls : List LayerTy}
    (hc : Checker.checkLayers sig p (.cons h t) = .ok ls) : ∃ x xs, ls = x :: xs := by
  simp only [Checker.checkLayers] at hc
  cases hh : Checker.checkLayer sig (p ++ [0]) h with
  | error r =>
    rw [hh] at hc
    cases hc
  | ok x =>
    rw [hh] at hc
    cases ht : Checker.checkLayers sig (p ++ [1]) t with
    | error r =>
      rw [ht] at hc
      cases hc
    | ok xs =>
      rw [ht] at hc
      cases hc
      exact ⟨x, xs, rfl⟩

/-- **The module layers' verdict, read at the block's child `2`, is the module check's
layers**: its answer refuses exactly where `Checker.checkLayers` at `2` refuses, and its table
is `Table.moduleLayers`. The part provides the layers to a unit program
(`Part.layersProgram`), and its child `0 :: 0 :: rest` is the block's `2 :: rest`. A step of
`checker-combine-deps`. Its consumer is `joinModule_deps`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem layers_join (app : SigApp) (holes : RowTable) (decls : List DefDecl)
    (h : LayerTerm NativeOp) (t : LayerTerms NativeOp) :
    ((run (.part ⟨app, holes, .block decls⟩ [] (Part.layersProgram (.cons h t)))).result.map
        (fun _ => ())).mapError layerRefusal =
        (Checker.checkLayers ((app.withHoles holes).signature.withDefs decls) [2] (.cons h t)).map
          (fun _ => ()) ∧
      layerTable (run (.part ⟨app, holes, .block decls⟩ [] (Part.layersProgram (.cons h t)))) =
        Table.moduleLayers ((app.withHoles holes).signature.withDefs decls) (.cons h t) := by
  constructor
  · have hv : (run (.part ⟨app, holes, .block decls⟩ [] (Part.layersProgram (.cons h t)))).result =
        Checker.check ((app.withHoles holes).signature.withDefs decls) [] []
          (Part.layersProgram (.cons h t)) := by
      show (Annotate.check _ [] [] _).2 = _
      rw [Annotate.check_eq]
      rfl
    rw [hv]
    have h00 := Checker.checkLayers_rebase ((app.withHoles holes).signature.withDefs decls) [0, 0]
      [] (.cons h t)
    have h2 := Checker.checkLayers_rebase ((app.withHoles holes).signature.withDefs decls) [2] []
      (.cons h t)
    simp only [List.append_nil] at h00 h2
    simp only [Part.layersProgram, Checker.check, Checker.checkLayer, List.nil_append,
      List.singleton_append, h00, h2]
    cases hc : Checker.checkLayers ((app.withHoles holes).signature.withDefs decls) [] (.cons h t) with
    | error r => rfl
    | ok ls =>
      obtain ⟨x, xs, rfl⟩ := checkLayers_cons_ok hc
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (mergeNonempty_cons_isSome x xs)
      simp only [Except.mapError, ok_bind, hm]
      rfl
  · have hv : (run (.part ⟨app, holes, .block decls⟩ [] (Part.layersProgram (.cons h t)))).table =
        tableAt ((app.withHoles holes).signature.withDefs decls) (some (.env []))
          (.eff (Part.layersProgram (.cons h t))) [] := by
      show (Annotate.check _ [] [] _).1 = _
      rw [Annotate.check_eq]
      rfl
    have hm : Table.moduleLayers ((app.withHoles holes).signature.withDefs decls) (.cons h t) =
        (tableAt ((app.withHoles holes).signature.withDefs decls) (some .closed)
          (.layers (.cons h t)) []).map (Table.Entry.rebase [2]) := by
      show (Annotate.checkLayers _ [2] _).1 = _
      rw [Annotate.checkLayers_eq, ← tableAt_rebase]
      rfl
    have h00 := tableAt_rebase ((app.withHoles holes).signature.withDefs decls) (some .closed)
      (.layers (.cons h t)) [0, 0] []
    rw [List.append_nil] at h00
    have hroot := tableAt_eq_cons ((app.withHoles holes).signature.withDefs decls) (some (.env []))
      (.eff (Part.layersProgram (.cons h t))) []
    have hlayer := tableAt_eq_cons ((app.withHoles holes).signature.withDefs decls) (some .closed)
      (.layer (.mergeAll (.cons h t))) [0]
    have hunit := tableAt_eq_cons ((app.withHoles holes).signature.withDefs decls) (some (.env []))
      (.eff (.succeed (.lit .unit))) [1]
    have c0 : childTableAt ((app.withHoles holes).signature.withDefs decls) (some (.env []))
        (.eff (Part.layersProgram (.cons h t))) [] 0 =
        tableAt ((app.withHoles holes).signature.withDefs decls) (some .closed)
          (.layer (.mergeAll (.cons h t))) [0] := rfl
    have c1 : childTableAt ((app.withHoles holes).signature.withDefs decls) (some (.env []))
        (.eff (Part.layersProgram (.cons h t))) [] 1 =
        tableAt ((app.withHoles holes).signature.withDefs decls) (some (.env []))
          (.eff (.succeed (.lit .unit))) [1] := rfl
    have c2 : childTableAt ((app.withHoles holes).signature.withDefs decls) (some (.env []))
        (.eff (Part.layersProgram (.cons h t))) [] 2 = [] := rfl
    have l0 : childTableAt ((app.withHoles holes).signature.withDefs decls) (some .closed)
        (.layer (.mergeAll (.cons h t))) [0] 0 =
        tableAt ((app.withHoles holes).signature.withDefs decls) (some .closed)
          (.layers (.cons h t)) [0, 0] := rfl
    have l1 : childTableAt ((app.withHoles holes).signature.withDefs decls) (some .closed)
        (.layer (.mergeAll (.cons h t))) [0] 1 = [] := rfl
    have l2 : childTableAt ((app.withHoles holes).signature.withDefs decls) (some .closed)
        (.layer (.mergeAll (.cons h t))) [0] 2 = [] := rfl
    have u0 : childTableAt ((app.withHoles holes).signature.withDefs decls) (some (.env []))
        (.eff (.succeed (.lit .unit))) [1] 0 = [] := rfl
    have u1 : childTableAt ((app.withHoles holes).signature.withDefs decls) (some (.env []))
        (.eff (.succeed (.lit .unit))) [1] 1 = [] := rfl
    have u2 : childTableAt ((app.withHoles holes).signature.withDefs decls) (some (.env []))
        (.eff (.succeed (.lit .unit))) [1] 2 = [] := rfl
    unfold layerTable
    rw [hv, hm, hroot, c0, c1, c2, hlayer, l0, l1, l2, hunit, u0, u1, u2, h00]
    simp only [List.append_nil, List.filterMap_cons, List.filterMap_append, List.filterMap_map,
      List.filterMap_nil]
    exact filterMap_eq_map_of (fun e => layerEntry_rebase e) _

/-- A program with no block is checked at the root. A step of `checker-combine-deps`. Its
consumer is `joinModule_deps`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem checkModule_plain {sig : Signature NativeOp} {e : NativeEff} (h : e.isBlock = false) :
    Checker.checkModule sig e = Checker.check sig [] [] e := by
  unfold Checker.checkModule
  split
  · cases h
  · rfl

/-- A statement whose answer is mapped to the unit binds as the answer does. A step of
`checker-combine-deps`. Its consumer is `joinModule_deps`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem map_unit_bind {ε α β : Type} (x : Except ε α) (k : Except ε β) :
    (x.map (fun _ => ()) >>= fun _ => k) = (x >>= fun _ => k) := by
  cases x <;> rfl

/-- **A module's dependency answers, joined, are its uncached verdict.** A program with no block
is one part at the root. A block's bodies, main program and module layers are joined in the
module check's order (`joinBodies_deps`, `layers_join`). The ill-formed reference's refusal and
the source's addresses then apply to the whole, as `Sketch.sourceCheck` and
`Sketch.sourceAnnotate` apply them. A step of `checker-combine-deps`. Its consumer is
`combine_deps`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem joinModule_deps (app : SigApp) (holes : RowTable) (p : NativeEff) :
    joinModule app holes p ((deps (.module app holes p)).map (fun d => run d.input)) =
      some (run (.module app holes p)) := by
  cases hb : p.expandRefs.isBlock
  · have hdeps : deps (.module app holes p) =
        [⟨.main, [], .part ⟨app, holes, .root⟩ [] p.expandRefs⟩] := by
      simp only [deps]
      split
      · rename_i h
        rw [h] at hb
        cases hb
      · rfl
    have hjoin : ∀ v : Verdict, joinModule app holes p [v] =
        some ⟨match p.firstRefFault with
          | some (site, target, why) => .error ⟨site, .referenceIllFormed target why⟩
          | none => v.result,
          Table.atSource ({ program := p, holes } : Sketch).sites p.firstRefFault v.table⟩ := by
      intro v
      simp only [joinModule]
      split
      · rename_i h
        rw [h] at hb
        cases hb
      · rfl
    rw [hdeps, List.map_cons, List.map_nil, hjoin]
    simp only [run, Sketch.sourceCheck, Sketch.sourceAnnotate, Sketch.expand, Sketch.check,
      Sketch.annotate, checkModule_plain hb, annotateModule_plain hb, annotate, Annotate.check_eq]
    rfl
  · obtain ⟨decls, bodies, main, layers, hx⟩ := Eff.eq_defs_of_isBlock hb
    have hmain : (place [1] (run (.part ⟨app, holes, .block decls⟩ [] main))).result =
        Checker.check ((app.withHoles holes).signature.withDefs decls) [] [1] main := by
      rw [run_placed, Annotate.check_eq]
      rfl
    have hmainT : (place [1] (run (.part ⟨app, holes, .block decls⟩ [] main))).table =
        (Annotate.check ((app.withHoles holes).signature.withDefs decls) [] [1] main).1 := by
      rw [run_placed]
      rfl
    cases layers with
    | nil =>
      have hj := joinBodies_deps app holes decls bodies decls 0 [0]
        [run (.part ⟨app, holes, .block decls⟩ [] main)]
      simp only [joinModule, deps, hx, List.map_append, List.map_cons, List.map_nil,
        List.append_nil, hj, Option.bind_eq_bind, Option.bind_some, hmain, hmainT]
      simp only [run, Sketch.sourceCheck, Sketch.sourceAnnotate, Sketch.expand, Sketch.check,
        Sketch.annotate, hx, Checker.checkModule, annotateModule]
      rfl
    | cons h t =>
      have hj := joinBodies_deps app holes decls bodies decls 0 [0]
        [run (.part ⟨app, holes, .block decls⟩ [] main),
          run (.part ⟨app, holes, .block decls⟩ [] (Part.layersProgram (.cons h t)))]
      obtain ⟨hl, ht⟩ := layers_join app holes decls h t
      simp only [joinModule, deps, hx, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.cons_append, List.nil_append, hj, Option.bind_eq_bind,
        Option.bind_some, hmain, hmainT, hl, ht]
      simp only [run, Sketch.sourceCheck, Sketch.sourceAnnotate, Sketch.expand, Sketch.check,
        Sketch.annotate, hx, Checker.checkModule, annotateModule, map_unit_bind]
      rfl

/-- **A key's dependency answers, combined, are its uncached verdict**: at a module key, the
check through the references and the source table, part by part (`joinModule_deps`); a part key
has no dependency and is its own run. So `Checked.ask` answers `run` at every key, and a memo or
an oracle behind it changes cost, never an answer. The pointer of `checker-combine-deps`. Reach:
every module and part key, refused ones and ill-formed references included. Not established:
admission, native execution, progress, or the cost of the parts. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem combine_deps (i : CheckInput) : combine i ((deps i).map (fun d => run d.input)) = run i := by
  cases i with
  | part sig env program => rfl
  | module app holes p =>
    unfold combine
    simp only [List.length_map, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, joinModule_deps]

/-- **Every ask answers the uncached verdict.** A part key asks the oracle once; a module key
combines its dependencies' answers, which `combine_deps` proves exact. The pointer of
`checker-ask-value`. -/
@[semantics "host-session-protocol" (requirement := R14)]
theorem Checked.ask_value (o : Oracle) (i : CheckInput) : (Checked.ask o i).value = run i := by
  rw [Oracle.eq_uncached o]
  cases i with
  | part sig env program => rfl
  | module app holes program =>
    change combine (.module app holes program)
      (((deps (.module app holes program)).map (fun d => (d.input, run d.input))).map Prod.snd) = _
    rw [List.map_map]
    exact combine_deps _
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem run_module (app : SigApp) (holes : RowTable) (program : NativeEff) :
    run (.module app holes program) =
      ⟨({ program,holes } : Sketch).sourceCheck app,({ program,holes } : Sketch).sourceAnnotate app⟩ := rfl

@[semantics "initial-algebras-folds" (requirement := R14)]
theorem run_part (sig : SigData) (env : TyEnv) (program : NativeEff) :
    run (.part sig env program) =
      ⟨(Annotate.check sig.signature env [] program).2,(Annotate.check sig.signature env [] program).1⟩ := rfl

/-- Placement: initial-algebras-folds, run_part_extends helper, positive part support, R14.
Consumer: positive extension-hit retention. This establishes no negative-answer or module reuse. -/
theorem support_of_positive {Op : Type} (sig : Signature Op) (program : Eff Op)
    (env : TyEnv) (ty : EffTy) (hp : Checker.check sig env [] program = .ok ty) :
    supportB sig program = true := by
  rw [supportB_eq]
  exact hasTy_sigProgram (check_sound sig program env [] ty hp)

theorem extension_hit_retains_positive (a b : SigData) (env : TyEnv) (q : NativeEff) (t : EffTy)
    (he : a.extendsB b = true) (hp : (run (.part a env q)).result = .ok t) :
    extension.hit (.part b env q) (.part a env q, run (.part a env q)) = true := by
  have hc : Checker.check a.signature env [] q = .ok t := by
    simpa only [run, Annotate.check_eq] using hp
  have hs := support_of_positive a.signature q env t hc
  have pos : (run (.part a env q)).result.toBool = true := by rw [hp]; rfl
  simp only [extension, extensionHit, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨True.intro,True.intro⟩,he⟩,pos⟩,hs⟩

def ExplanationReplays (input key : CheckInput) (why : TypeRefusal) : Prop :=
  match input with
  | .part .. => key = input ∧ (run key).result = .error why
  | .module .. => ∃ dependency ∈ Internal.deps input,
      dependency.input = key ∧ locatedResult dependency (run key) = .error why

@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal explain_replays (o : Oracle) (input : CheckInput) (explanation : Explanation)
    (key : CheckInput) (he : (explain o input).value = some explanation)
    (hp : explanation.part = some key) : ExplanationReplays input key explanation.refusal

end Effect4.Program.Check
