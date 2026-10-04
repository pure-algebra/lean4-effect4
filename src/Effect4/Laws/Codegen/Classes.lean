import Effect4.Codegen.ClassTable
import Effect4.Laws.Codegen.Record

/-!
# Laws.Codegen.Classes — the payload class images, exact (decisions row 120, part E2)

Concept: Translation & Simulation Metatheory (`translation-simulation`), at R8: these are the
steps of the term round trip's class branch (`readTerm_printTerm`, `readTerm_exact`,
`Laws/Codegen/ReadLeaf.lean`) and of the module round trip's class section
(`readModule_printModule`, `Laws/Codegen/Module.lean`), whose consumers are `read_print`,
`read_exact` and the emitted module's reading. Reach: every expression, every class table; the
construction image needs no typing premise (decisions row 165: the reader is untyped).

What they do not establish: that tsgo accepts a printed class (finite controls,
`ts/eff/test/payload-classes.typecheck.ts`), or that a class's declaration reads back: that is
decided where the module prints (`ClassTable.checkedDecl`), and `readClassDecls_checked` uses
the decision, never assumes it.
-/

set_option autoImplicit false

namespace Effect4.Codegen.Classes

open Effect4.Program TypeScript

/-! ## The construction -/

/-- A construction reads back: its tag, its names and its value expressions, when every name has
its value. Step of `readTerm_printTerm`'s class branch (R8). -/
theorem readClass_writeClass (tag : String) (names : List String) (values : List Expr)
    (hlen : names.length = values.length) :
    readClass (writeClass tag names values) = some (tag, names, values) := by
  have hf := List.map_fst_zip (Nat.le_of_eq hlen)
  have hs := List.map_snd_zip (Nat.le_of_eq hlen.symm)
  simp only [writeClass, readClass, Record.readProperties_properties, Option.bind_some, hf, hs,
    ↓reduceIte]

/-- What the construction reader accepts is exactly a construction: the `new` of the tag at the
object of its names and values in their key form. Step of `readTerm_exact` (R8). -/
theorem readClass_exact (e : Expr) (tag : String) (names : List String) (values : List Expr)
    (h : readClass e = some (tag, names, values)) : writeClass tag names values = e := by
  unfold readClass at h
  split at h
  · next tag' form entries =>
    obtain ⟨pairs, hpairs, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · next hform =>
      cases h
      simp only [writeClass]
      rw [Record.properties_fst_snd, Record.readProperties_exact entries pairs hpairs, ← hform]
    · exact nomatch h
  · exact nomatch h

/-- The structural record's image is no construction. -/
theorem readClass_writeRecord (fields : Fields) (names : List String) (values : List Expr) :
    readClass (Record.writeRecord fields names values) = none := by
  unfold Record.writeRecord
  split <;> rfl

/-- A field read's image is no construction. -/
theorem readClass_writeField (optional : Bool) (name : String) (target : Expr) :
    readClass (Record.writeField optional name target) = none := by
  cases optional <;> rfl

/-- An update's image is no construction. -/
theorem readClass_writeSet (name : String) (target value : Expr) :
    readClass (Record.writeSet name target value) = none := rfl

/-- A tuple projection's image is no construction. -/
theorem readClass_writeAt (index : Nat) (target : Expr) :
    readClass (Tuple.writeAt index target) = none := rfl

/-! ## The class form -/

/-- What a class form says of a construction: its fields are a payload class with `_tag` first,
its names begin with `_tag` and repeat it nowhere after, its values begin with the tag's
literal, and the other names pair one for one with the other values. -/
theorem classTag?_some {fields : Fields} {names : List String} {values : Terms} {tag : String}
    (h : classTag? fields names values = some tag) :
    Types.payloadClass? fields = some tag ∧ fields.head? = some ("_tag", false, .lit tag) ∧
      names = "_tag" :: names.tail ∧ values = .cons (.lit (.str tag)) (restTerms values) ∧
      "_tag" ∉ names.tail ∧ names.tail.length = (restTerms values).toList.length := by
  unfold classTag? at h
  obtain ⟨tag', hp, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · next hc =>
    cases h
    obtain ⟨hf, hn, hv, hrep, hlen⟩ := hc
    refine ⟨hp, hf, ?_, ?_, hrep, hlen⟩
    · cases names with
      | nil => cases hn
      | cons head tail =>
        simp only [List.head?_cons, Option.some.injEq] at hn
        subst hn
        rfl
    · cases values with
      | nil => cases hv
      | cons head tail =>
        simp only [firstTerm, Option.some.injEq] at hv
        subst hv
        rfl
  · exact nomatch h

/-- The tail of a list's printing is the printing of its tail. -/
theorem printTerms_restTerms (values : Terms) : (printTerms values).tail = printTerms (restTerms values) := by
  cases values <;> rfl

/-- The printed tail's length is the tail's. -/
theorem printTerms_length : ∀ (values : Terms), (printTerms values).length = values.toList.length
  | .nil => rfl
  | .cons _ tail => by
    simp only [printTerms, List.length_cons, Terms.toList, printTerms_length tail]

/-! ## The class declaration -/

/-- A checked declaration reads back to its class. Step of `readClassDecls_checked`. -/
theorem readClassDecl_checked {entry : String × Fields} {c : ClassDecl}
    (h : ClassTable.checkedDecl entry = .ok c) : readClassDecl c = some entry := by
  unfold ClassTable.checkedDecl at h
  split at h
  · split at h
    · next hread =>
      cases h
      exact hread
    · exact nomatch h
  · exact nomatch h

/-- **A module's checked class declarations read back to its classes**, in order (decisions row
120): the module round trip's class section (`readModule_printModule`, R8). The premise is the
module printer's own decision (`ClassTable.moduleClasses` runs `checkedDecl` on every class). -/
theorem readClassDecls_checked : ∀ {table : Classes} {decls : List ClassDecl},
    table.mapM ClassTable.checkedDecl = .ok decls → readClassDecls decls = some table
  | [], decls, h => by
    cases h
    rfl
  | entry :: rest, decls, h => by
    simp only [List.mapM_cons, bind, Except.bind] at h
    split at h
    · exact nomatch h
    · next c hc =>
      split at h
      · exact nomatch h
      · next cs hcs =>
        cases h
        simp only [readClassDecls, List.mapM_cons, readClassDecl_checked hc]
        have ih := readClassDecls_checked hcs
        simp only [readClassDecls] at ih
        simp only [ih]
        rfl

/-- What the class reader accepts is exactly a printed declaration: the one `classDecl` prints for
the class it reads to (decisions row 120). With `readClassDecl_checked`, the declaration's exact
embedding. Step of `readClassDecls_eq_checked`. -/
theorem readClassDecl_exact {c : ClassDecl} {entry : String × Fields}
    (h : readClassDecl c = some entry) : classDecl entry.1 entry.2 = some c := by
  obtain ⟨doc, name, heritage, members, exported⟩ := c
  unfold readClassDecl at h
  split at h
  · next head tag fs hheritage =>
    obtain ⟨rest, _, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h hheritage
    split at h
    · next hc =>
      cases h
      obtain ⟨rfl, hdoc, hname, hmembers, hexported, hfs⟩ := hc
      obtain ⟨fs', hfs', hobj⟩ := Option.map_eq_some_iff.mp hfs
      cases hobj
      subst hheritage hdoc hname hmembers hexported
      simp only [classDecl, hfs', Option.map_some]
    · exact nomatch h
  · exact nomatch h

/-- A checked declaration is the class's printed declaration. Step of
`readClassDecls_eq_checked`. -/
theorem checkedDecl_classDecl {entry : String × Fields} {c : ClassDecl}
    (h : ClassTable.checkedDecl entry = .ok c) : classDecl entry.1 entry.2 = some c := by
  unfold ClassTable.checkedDecl at h
  split at h
  · next c' hc' =>
    split at h
    · cases h
      exact hc'
    · exact nomatch h
  · exact nomatch h

/-- **Declarations that read back to a table are the table's checked declarations** (decisions
row 120): the module's class section has one spelling. Step of `admitModule_classDecls` (R3). -/
theorem readClassDecls_eq_checked : ∀ {cs : List ClassDecl} {table : Classes} {ds : List ClassDecl},
    readClassDecls cs = some table → table.mapM ClassTable.checkedDecl = .ok ds → cs = ds
  | [], table, ds, hread, hchecked => by
    simp only [readClassDecls, List.mapM_nil, pure, Option.some.injEq] at hread
    subst hread
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hchecked
    exact hchecked
  | c :: cs, table, ds, hread, hchecked => by
    simp only [readClassDecls, List.mapM_cons, bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at hread
    obtain ⟨entry, hentry, rest, hrest, rfl⟩ := hread
    simp only [List.mapM_cons, bind, Except.bind] at hchecked
    split at hchecked
    · exact nomatch hchecked
    · next d hd =>
      split at hchecked
      · exact nomatch hchecked
      · next ds' hds =>
        cases hchecked
        have same : c = d :=
          Option.some.inj ((readClassDecl_exact hentry).symm.trans (checkedDecl_classDecl hd))
        rw [same, readClassDecls_eq_checked hrest hds]

end Effect4.Codegen.Classes

namespace Effect4.Program

open Effect4.Codegen.Classes (Classes)

variable {classes : Classes}

/-! ## Coverage, node by node (the generated fold's equations)

Steps of `readTerm_printTerm` and of the row lemmas in `Laws/Codegen/ReadLeaf.lean` (R8): the
round trip splits a covered term into its node's coverage and its children's. -/

theorem Term.covers_app (atom : String) (args : Terms) :
    Term.covers classes (.app atom args) = Terms.covers classes args := rfl
theorem Term.covers_record (fields : List (String × Bool × Ty)) (names : List String) (values : Terms) :
    Term.covers classes (.record fields names values) =
      (coverNode classes (.record fields names values) && Terms.covers classes values) := rfl
theorem Term.covers_field (mode : FieldReadMode) (target : Term) (name : String) :
    Term.covers classes (.field mode target name) = Term.covers classes target := rfl
theorem Term.covers_recordSet (target : Term) (name : String) (value : Term) :
    Term.covers classes (.recordSet target name value) =
      (Term.covers classes target && Term.covers classes value) := rfl
theorem Term.covers_tupleAt (target : Term) (index : Nat) :
    Term.covers classes (.tupleAt target index) = Term.covers classes target := rfl
theorem Terms.covers_cons (t : Term) (ts : Terms) :
    Terms.covers classes (.cons t ts) = (Term.covers classes t && Terms.covers classes ts) := rfl

theorem CauseTerm.covers_fail (t : Term) :
    CauseTerm.covers classes (.fail t) = Term.covers classes t := rfl
theorem CauseTerm.covers_die (t : Term) :
    CauseTerm.covers classes (.die t) = Term.covers classes t := rfl
theorem CauseTerm.covers_interrupt (who : Option Term) :
    CauseTerm.covers classes (.interrupt who) = who.all (Term.covers classes) := rfl
theorem CauseTerm.covers_both (left right : CauseTerm) :
    CauseTerm.covers classes (.both left right) =
      (CauseTerm.covers classes left && CauseTerm.covers classes right) := rfl

/-- A covered class construction names its class with its declared fields. -/
theorem coverNode_class {fields : List (String × Bool × Ty)} {names : List String} {values : Terms}
    {tag : String} (h : coverNode classes (.record fields names values) = true)
    (hc : Codegen.Classes.classTag? fields names values = some tag) :
    classes.lookup tag = some fields := by
  simp only [coverNode, hc, decide_eq_true_eq] at h
  exact h

/-- No class construction is covered by every table: every term with none is covered. A literal
holds no record (`readLiteral` reads under no class). -/
theorem Term.covers_lit_nil (v : Lit) : Term.covers [] (.lit v) = true := rfl

end Effect4.Program
