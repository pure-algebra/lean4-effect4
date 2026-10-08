import Effect4.Modules.Step
import Effect4.Laws.Modules.Step.Annotations

/-! Annotation-independent interpretation of the existing Step algebra.
Placement: helper of step-language-sound and Queue operation agreement,
translation-simulation, R10. Source refusal, names, values, indices, and scope insertion remain.
This interpretation establishes no typing or membership statement. -/
set_option autoImplicit false
namespace Effect4.Modules
open Effect4.Program Effect4.Program.Authoring Effect4.Store Effect4.Schema

def eraseSource (src : TermSrc) : TermSrc := fun env path => (src env path).map Term.eraseAnnotations

/-- Reuse the compiler's scope machinery and erase at each resolved input.
Only annotation-bearing construction changes. -/
def Step.erasedTermAlg : StepAlgebra (fun Γ _ => ({t : Ty} → Input Γ t → TermSrc) → TermSrc) :=
  { Step.termAlg with
    var := fun x src => eraseSource (src x)
    record := fun {_Γ} {fs} fields src =>
      Authoring.record [] (FieldResults.map (fun name {_} value => (name, value src)) fs fields)
    nil := fun _ => field (Authoring.record [] [("v", nilT)]) "v"
    none := fun _ => field (Authoring.record [] [("v", noneT)]) "v" }

/-- Erasing a generated value list commutes with reconstructing Terms.
A helper of the compiler's app and record cases. -/
theorem erase_termsOfList : (ts : List Term) →
    (termsOfList ts).eraseAnnotations = termsOfList (ts.map Term.eraseAnnotations)
  | [] => rfl
  | t :: ts => by
    change Terms.cons t.eraseAnnotations (termsOfList ts).eraseAnnotations =
      Terms.cons t.eraseAnnotations (termsOfList (ts.map Term.eraseAnnotations))
    rw [erase_termsOfList ts]

/-- Resolve source children and erase their successful trees.
Refusal remains the first refused child. -/
theorem sources_erase (env : Env) (path : List Nat) : (xs : List TermSrc) →
    (xs.mapM (fun (src : TermSrc) => src env path)).map (List.map Term.eraseAnnotations) =
      (xs.map eraseSource).mapM (fun (src : TermSrc) => src env path)
  | [] => rfl
  | src :: rest => by
    simp only [List.map_cons, List.mapM_cons]
    rw [← sources_erase env path rest]
    simp only [eraseSource]
    cases head : src env path <;> cases tail : rest.mapM (fun (src : TermSrc) => src env path) <;> rfl

/-- App compilation commutes with erasure of the successful child trees. -/
theorem eraseSource_app (atom : String) (args : List TermSrc) :
    eraseSource (app atom args) = app atom (args.map eraseSource) := by
  funext env path
  change (do
    let values ← args.mapM (fun (src : TermSrc) => src env path)
    Except.ok (Term.app atom (termsOfList values))).map Term.eraseAnnotations =
    (do
      let values ← (args.map eraseSource).mapM (fun (src : TermSrc) => src env path)
      Except.ok (Term.app atom (termsOfList values)))
  rw [← sources_erase env path args]
  cases tree : args.mapM (fun (src : TermSrc) => src env path) with
  | error _ => rfl
  | ok values =>
    change Except.ok (Term.app atom (termsOfList values).eraseAnnotations) =
      Except.ok (Term.app atom (termsOfList (values.map Term.eraseAnnotations)))
    rw [erase_termsOfList values]

/-- A field retains its mode and name under annotation erasure. -/
theorem eraseSource_field (src : TermSrc) (name : String) :
    eraseSource (field src name) = field (eraseSource src) name := by
  funext env path
  change (do let t ← src env path; Except.ok (Term.field .required t name)).map Term.eraseAnnotations =
    (do let t ← (src env path).map Term.eraseAnnotations; Except.ok (Term.field .required t name))
  cases tree : src env path <;> rfl

/-- An overwrite retains its name and value children under annotation erasure. -/
theorem eraseSource_set (src value : TermSrc) (name : String) :
    eraseSource (recordSet src name value) = recordSet (eraseSource src) name (eraseSource value) := by
  funext env path
  change (do let t ← src env path; let v ← value env path; Except.ok (Term.recordSet t name v)).map Term.eraseAnnotations =
    (do
      let t ← (src env path).map Term.eraseAnnotations
      let v ← (value env path).map Term.eraseAnnotations
      Except.ok (Term.recordSet t name v))
  cases target : src env path <;> cases replacement : value env path <;> rfl

/-- Record compilation retains names and erases only the ignored declaration. -/
theorem eraseSource_record (fs : List (String × Bool × Ty)) (present : List (String × TermSrc)) :
    eraseSource (Authoring.record fs present) =
      Authoring.record [] (present.map (fun p => (p.1, eraseSource p.2))) := by
  funext env path
  simp only [eraseSource, Authoring.record, List.map_map, List.mapM_map, Function.comp_def]
  have children := sources_erase env path (present.map Prod.snd)
  simp only [List.mapM_map, List.map_map, Function.comp_def, eraseSource] at children
  rw [← children]
  cases tree : present.mapM (fun p => p.2 env path) with
  | error _ => rfl
  | ok values =>
    change Except.ok (Term.record [] (present.map Prod.fst) (termsOfList values).eraseAnnotations) =
      Except.ok (Term.record [] (present.map Prod.fst) (termsOfList (values.map Term.eraseAnnotations)))
    rw [erase_termsOfList values]

/-- A literal has no annotation to erase. -/
theorem eraseSource_lit (value : Lit) : eraseSource (lit value) = lit value := rfl

mutual
/-- Erasure of the ordinary compiler equals the annotation-independent interpretation.
The consumer is the Queue A/P connector, retaining every source refusal and captured scope. -/
theorem Step.term_erase : {Γ : List Ty} → {t : Ty} → (e : Step Γ t) →
    (src : {u : Ty} → Input Γ u → TermSrc) →
    eraseSource (e.term src) = Step.cata Step.erasedTermAlg e src
  | _, _, .tuple (ts := ts) xs, src => by
    change eraseSource (Authoring.tuple (ItemResults.map (fun {_} x => x src) ts (Step.cataItems Step.termAlg xs))) = _
    unfold Authoring.tuple
    rw [eraseSource_app, Step.items_erase xs src]
    rfl
  | _, _, .var _, _ => rfl
  | _, _, .bool _, _ => rfl
  | _, _, .nat _, _ => rfl
  | _, _, .unit, _ => rfl
  | _, _, .not a, src => by
    change eraseSource (notT (a.term src)) = notT (Step.cata Step.erasedTermAlg a src)
    simp only [notT, eraseSource_app, List.map_cons, List.map_nil, Step.term_erase a src]
  | _, _, .and a b, src => by
    change eraseSource (andT (a.term src) (b.term src)) = andT (Step.cata Step.erasedTermAlg a src) (Step.cata Step.erasedTermAlg b src)
    simp only [andT, eraseSource_app, List.map_cons, List.map_nil, Step.term_erase a src, Step.term_erase b src]
  | _, _, .or a b, src => by
    change eraseSource (orT (a.term src) (b.term src)) = orT (Step.cata Step.erasedTermAlg a src) (Step.cata Step.erasedTermAlg b src)
    simp only [orT, eraseSource_app, List.map_cons, List.map_nil, Step.term_erase a src, Step.term_erase b src]
  | _, _, .ite c a b, src => by
    change eraseSource (ifT (c.term src) (a.term src) (b.term src)) = ifT (Step.cata Step.erasedTermAlg c src) (Step.cata Step.erasedTermAlg a src) (Step.cata Step.erasedTermAlg b src)
    simp only [ifT, eraseSource_app, List.map_cons, List.map_nil, Step.term_erase c src, Step.term_erase a src, Step.term_erase b src]
  | _, _, .add a b, src => by
    change eraseSource (app "add" [a.term src, b.term src]) = app "add" [Step.cata Step.erasedTermAlg a src, Step.cata Step.erasedTermAlg b src]
    simp only [eraseSource_app, List.map_cons, List.map_nil, Step.term_erase a src, Step.term_erase b src]
  | _, _, .sub a b, src => by
    change eraseSource (app "sub" [a.term src, b.term src]) = app "sub" [Step.cata Step.erasedTermAlg a src, Step.cata Step.erasedTermAlg b src]
    simp only [eraseSource_app, List.map_cons, List.map_nil, Step.term_erase a src, Step.term_erase b src]
  | _, _, .lt a b, src => by
    change eraseSource (app "lt" [a.term src, b.term src]) = app "lt" [Step.cata Step.erasedTermAlg a src, Step.cata Step.erasedTermAlg b src]
    simp only [eraseSource_app, List.map_cons, List.map_nil, Step.term_erase a src, Step.term_erase b src]
  | _, _, .eq a b, src => by
    change eraseSource (app "eq" [a.term src, b.term src]) = app "eq" [Step.cata Step.erasedTermAlg a src, Step.cata Step.erasedTermAlg b src]
    simp only [eraseSource_app, List.map_cons, List.map_nil, Step.term_erase a src, Step.term_erase b src]
  | _, _, .isZero a, src => by
    change eraseSource (app "isZero" [a.term src]) = app "isZero" [Step.cata Step.erasedTermAlg a src]
    simp only [eraseSource_app, List.map_cons, List.map_nil, Step.term_erase a src]
  | _, _, .pair a b, src => by
    change eraseSource (app "pair" [a.term src, b.term src]) = app "pair" [Step.cata Step.erasedTermAlg a src, Step.cata Step.erasedTermAlg b src]
    simp only [eraseSource_app, List.map_cons, List.map_nil, Step.term_erase a src, Step.term_erase b src]


  | _, _, .fst a, src => by
    change eraseSource (app "fst" [a.term src]) = app "fst" [Step.cata Step.erasedTermAlg a src]
    simp only [eraseSource_app, List.map_cons, List.map_nil, Step.term_erase a src]
  | _, _, .snd a, src => by
    change eraseSource (app "snd" [a.term src]) = app "snd" [Step.cata Step.erasedTermAlg a src]
    simp only [eraseSource_app, List.map_cons, List.map_nil, Step.term_erase a src]
  | _, _, .some a, src => by
    change eraseSource (app "some" [a.term src]) = app "some" [Step.cata Step.erasedTermAlg a src]
    simp only [eraseSource_app, List.map_cons, List.map_nil, Step.term_erase a src]
  | _, _, .emptyLike a, src => by
    change eraseSource (noneOf (a.term src)) = noneOf (Step.cata Step.erasedTermAlg a src)
    simp only [noneOf, eraseSource_app, List.map_cons, List.map_nil, Step.term_erase a src, Authoring.nat, eraseSource_lit]
  | _, _, .len a, src => by
    change eraseSource (Modules.len (a.term src)) = Modules.len (Step.cata Step.erasedTermAlg a src)
    simp only [Modules.len, eraseSource_app, List.map_cons, List.map_nil, Step.term_erase a src]
  | _, _, .snoc a b, src => by
    change eraseSource (Modules.snoc (a.term src) (b.term src)) = Modules.snoc (Step.cata Step.erasedTermAlg a src) (Step.cata Step.erasedTermAlg b src)
    simp only [Modules.snoc, eraseSource_app, List.map_cons, List.map_nil, Step.term_erase a src, Step.term_erase b src, nilT]
  | _, _, .getOrElse a b, src => by
    change eraseSource (app "getOrElse" [a.term src, b.term src]) = app "getOrElse" [Step.cata Step.erasedTermAlg a src, Step.cata Step.erasedTermAlg b src]
    simp only [eraseSource_app, List.map_cons, List.map_nil, Step.term_erase a src, Step.term_erase b src]
  | _, _, .append a b, src => by
    change eraseSource (app "append" [a.term src, b.term src]) = app "append" [Step.cata Step.erasedTermAlg a src, Step.cata Step.erasedTermAlg b src]
    simp only [eraseSource_app, List.map_cons, List.map_nil, Step.term_erase a src, Step.term_erase b src]
  | _, _, .take a b, src => by
    change eraseSource (app "take" [a.term src, b.term src]) = app "take" [Step.cata Step.erasedTermAlg a src, Step.cata Step.erasedTermAlg b src]
    simp only [eraseSource_app, List.map_cons, List.map_nil, Step.term_erase a src, Step.term_erase b src]
  | _, _, .drop a b, src => by
    change eraseSource (app "drop" [a.term src, b.term src]) = app "drop" [Step.cata Step.erasedTermAlg a src, Step.cata Step.erasedTermAlg b src]
    simp only [eraseSource_app, List.map_cons, List.map_nil, Step.term_erase a src, Step.term_erase b src]
  | _, _, .head a, src => by
    change eraseSource (app "get" [a.term src, Authoring.nat 0]) = app "get" [Step.cata Step.erasedTermAlg a src, Authoring.nat 0]
    simp only [eraseSource_app, List.map_cons, List.map_nil, Step.term_erase a src, Authoring.nat, eraseSource_lit]
  | _, _, .cons a b, src => by
    change eraseSource (app "cons" [a.term src, b.term src]) = app "cons" [Step.cata Step.erasedTermAlg a src, Step.cata Step.erasedTermAlg b src]
    simp only [eraseSource_app, List.map_cons, List.map_nil, Step.term_erase a src, Step.term_erase b src]
  | _, _, .sameDeferred a b, src => by
    change eraseSource (Modules.same (a.term src) (b.term src)) = Modules.same (Step.cata Step.erasedTermAlg a src) (Step.cata Step.erasedTermAlg b src)
    simp only [Modules.same, eraseSource_app, List.map_cons, List.map_nil, Step.term_erase a src, Step.term_erase b src]
  | _, _, .get a f, src => by
    change eraseSource (field (a.term src) f.name) = _
    rw [eraseSource_field, Step.term_erase a src]
    rfl
  | _, _, .set a f b, src => by
    change eraseSource (recordSet (a.term src) f.name (b.term src)) = _
    rw [eraseSource_set, Step.term_erase a src, Step.term_erase b src]
    rfl
  | _, _, .record fields, src => by
    change eraseSource (Authoring.record _ (FieldResults.map (fun name {_} value => (name, value src)) _
      (Step.cataFields Step.termAlg fields))) = _
    rw [eraseSource_record, Step.fields_erase fields src]
    rfl
  | _, _, .nil, _ => by
    simp only [Step.term, Step.cata, Step.termAlg, Step.erasedTermAlg, ascribe,
      eraseSource_field, eraseSource_record, List.map_cons, List.map_nil, nilT, eraseSource_app]
  | _, _, .none, _ => by
    simp only [Step.term, Step.cata, Step.termAlg, Step.erasedTermAlg, ascribe,
      eraseSource_field, eraseSource_record, List.map_cons, List.map_nil, noneT, eraseSource_app]
  | _, _, .fold xs init body, src => by
    funext env path
    change (do
      let l ← xs.term src env path
      let i ← init.term src env path
      let b ← body.term (Step.foldSources src env path)
        (env.push [env.mint "acc", env.mint "item"]) path
      Except.ok (Term.fold Option.none l i b)).map Term.eraseAnnotations = _
    have hx := congrArg (fun f => f env path) (Step.term_erase xs src)
    have hi := congrArg (fun f => f env path) (Step.term_erase init src)
    have hb := congrArg (fun f => f (env.push [env.mint "acc", env.mint "item"]) path)
      (Step.term_erase body (Step.foldSources src env path))
    change _ = (do
      let l ← Step.cata Step.erasedTermAlg xs src env path
      let i ← Step.cata Step.erasedTermAlg init src env path
      let b ← Step.cata Step.erasedTermAlg body (Step.foldSources src env path)
        (env.push [env.mint "acc", env.mint "item"]) path
      Except.ok (Term.fold Option.none l i b))
    rw [← hx, ← hi, ← hb]
    simp only [eraseSource]
    cases hl : xs.term src env path <;> cases hh : init.term src env path <;>
      cases ht : body.term (Step.foldSources src env path)
        (env.push [env.mint "acc", env.mint "item"]) path <;> rfl
/-- The fields form serves the record case of Step.term_erase. -/
theorem Step.fields_erase : {Γ : List Ty} → {fs : List (String × Bool × Ty)} →
    (fields : StepFields Γ fs) → (src : {u : Ty} → Input Γ u → TermSrc) →
    (FieldResults.map (fun name {_} value => (name, value src)) fs (Step.cataFields Step.termAlg fields)).map
      (fun p => (p.1, eraseSource p.2)) =
    FieldResults.map (fun name {_} value => (name, value src)) fs (Step.cataFields Step.erasedTermAlg fields)
  | _, _, .nil, _ => rfl
  | _, _, .cons name value rest, src => by
    change (name, eraseSource (value.term src)) ::
      (FieldResults.map (fun name {_} value => (name, value src)) _ (Step.cataFields Step.termAlg rest)).map
        (fun p => (p.1, eraseSource p.2)) =
      (name, Step.cata Step.erasedTermAlg value src) ::
        FieldResults.map (fun name {_} value => (name, value src)) _ (Step.cataFields Step.erasedTermAlg rest)
    rw [Step.term_erase value src, Step.fields_erase rest src]

/-- Annotation erasure commutes with the typed tuple child fold. -/
theorem Step.items_erase : {Γ : List Ty} → {ts : List Ty} → (xs : StepItems Γ ts) →
    (src : {u : Ty} → Input Γ u → TermSrc) →
    (ItemResults.map (fun {_} x => x src) ts (Step.cataItems Step.termAlg xs)).map eraseSource =
    ItemResults.map (fun {_} x => x src) ts (Step.cataItems Step.erasedTermAlg xs)
  | _, _, .nil, _ => rfl
  | _, _, .cons x xs, src => by
    change eraseSource (x.term src) :: _ = Step.cata Step.erasedTermAlg x src :: _
    simp only [Step.cataItems] at *
    rw [Step.term_erase x src, Step.items_erase xs src]
end

end Effect4.Modules
