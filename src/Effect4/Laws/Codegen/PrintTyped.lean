import Effect4.Codegen.PrintTyped
import Effect4.Laws.Program.Typing.Call
import Effect4.Laws.Program.Typing.Focus
import Effect4.Codegen.EraseTypes
import Effect4.Laws.Codegen.ReadPrint
import Effect4.Laws.Codegen.PrintReadable

/-!
# Laws.Codegen.PrintTyped — reconstruction after named erasure

The empty row annotation agrees with the ordinary printer through fold uniqueness.
`printTyped_eq_print` keeps that equation under `NoJoin`.
Successful raw typed prints erase to ordinary prints on the existing readable fragment.
The existing reader's retraction and reconstruction laws follow through that equation.
Target typing and execution remain separate evidence.
-/

set_option autoImplicit false

namespace Effect4.Codegen.Templates

open Effect4.Program

variable {Op : Type}

/-- The plain print at every address is a homomorphism into the typed print's algebra at the
empty annotation: each field is its definition. A step of `printTypedAt_none`, the claim
`typed-print-connector`. -/
def noneHom (sig : Signature Op) : EffHom (typedAlg sig (fun _ => none)) := by
  refine'
    { f_eff := fun e _ => cata_eff (printAlg sig) e
      f_stmt := fun s _ => cata_stmt (printAlg sig) s
      f_stmts := fun s _ => cata_stmts (printAlg sig) s
      f_effs := fun s _ => cata_effs (printAlg sig) s
      f_action := fun a _ => cata_action (printAlg sig) a
      f_layer := fun l _ => cata_layer (printAlg sig) l
      f_layers := fun l _ => cata_layers (printAlg sig) l
      .. }
  all_goals (intros; rfl)

/-- **At the empty annotation the typed print is the print**, at every program and environment
length, by the uniqueness of the fold (`hom_eq_cata_eff`). A step of `printTyped_eq_print`; it
says nothing at an annotation that answers. -/
@[semantics "exact-codecs" (requirement := R8)]
theorem printTypedAt_none (sig : Signature Op) (n : Nat) (e : Eff Op) :
    printTypedAt sig (fun _ => none) n e = print sig n e := by
  unfold printTypedAt
  rw [← hom_eq_cata_eff (noneHom sig) e]
  rfl

/-- The existing typed algebra's row-call override at the generic layer seam.
This serves the raw typed-print erasure claim (exact-codecs, R8), through `typed_cata_build`. -/
def typedLayer (sig : Signature Op) (ann : List Nat → Option (List Ty)) :
    (fam : EffFam) → String → List (ArgF Op TCarrier) → TCarrier fam
  | .eff, "perform", [.op op, .term request] =>
      fun path n => printPerformAt sig n op request (ann path)
  | fam, ctor, args => fun path => tableLayer sig fam ctor (atAddress path args 0)

theorem typedAlg_ofLayer (sig : Signature Op) (ann : List Nat → Option (List Ty)) :
    typedAlg sig ann = EffAlgebra.ofLayer (typedLayer sig ann) := rfl

theorem typed_cata_build (sig : Signature Op) (ann : List Nat → Option (List Ty))
    (fam : EffFam) (ctor : String) (args : List (ArgF Op (EffSelfCarrier Op)))
    (e : EffSelfCarrier Op fam) (builds : build fam ctor args = some e) :
    cataFam (typedAlg sig ann) fam e =
      typedLayer sig ann fam ctor (args.map (ArgF.fold (typedAlg sig ann))) := by
  rw [typedAlg_ofLayer]
  exact cata_build (typedLayer sig ann) fam ctor args e builds

end Effect4.Codegen.Templates

namespace Effect4.Program

variable {Op : Type}

/-- Without a row join annotation, the typed print is the ordinary print.
This remains the pointer of `typed-print-connector`, exact-codecs, R8.
The `NoJoin` premise states absence at every checked address.
It makes no TypeScript typing or execution claim. -/
@[semantics "exact-codecs" (requirement := R8)]
theorem printTyped_eq_print (s : Signature Op) (env0 : TyEnv) (p : Eff Op)
    (noJoin : NoJoin s env0 p) :
    printTyped s env0 p = print s env0.length p := by
  have annotation : typeArgsAt s env0 p = fun _ => none := by
    funext path
    unfold typeArgsAt
    rw [noJoin path]
    rfl
  unfold printTyped
  rw [annotation]
  exact Effect4.Codegen.Templates.printTypedAt_none s env0.length p

end Effect4.Program

namespace Effect4.Codegen

open TypeScript
open Effect4.Program

variable {Op : Type} {classes : Classes.Classes} {sig : Signature Op}
  {spell : String → List String → Option Op}

/-- The target fold's list component is the list map of its expression component.
Its consumer is the template erasure relation of the proposed typed-print erasure claim. -/
theorem targetFold_exprs_map {E S O : Type} (alg : TargetFold.Algebra E S O)
    (xs : List Expr) : TargetFold.exprs alg xs = xs.map (TargetFold.expr alg) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [TargetFold.exprs, List.map_cons, ih]

/-- Arrays reconstruct after their children fold. A template erasure relation step. -/
theorem mapCalls_arr (call : Nat → Expr → Expr) (xs : List Expr) (n : Nat) :
    mapCalls call (.arr xs) n = .arr (xs.map fun x => mapCalls call x n) := by
  simp only [mapCalls, TargetFold.expr, callAlgebra, atDepth, targetFold_exprs_map, List.map_map]
  rfl

/-- Call reconstruction exposes only the transformed children and the call field.
Its consumer is the pure-leaf and template relation for typed-print erasure. -/
theorem mapCalls_call (call : Nat → Expr → Expr) (head : Expr) (xs : List Expr) (n : Nat) :
    mapCalls call (.call head xs) n = call n (.call (mapCalls call head n)
      (xs.map fun x => mapCalls call x n)) := by
  simp only [mapCalls, TargetFold.expr, callAlgebra, atDepth, targetFold_exprs_map, List.map_map]
  rfl

/-- A bare call head carries no argument to erase. A template and pure-leaf relation step. -/
theorem eraseRowJoin_call_ident (n : Nat) (name : String) (xs : List Expr) :
    eraseRowJoin classes sig spell n (.call (.ident name) xs) = .call (.ident name) xs := rfl

/-- Names reconstruct directly. A pure-leaf and template relation step. -/
theorem mapCalls_ident (call : Nat → Expr → Expr) (name : String) (n : Nat) :
    mapCalls call (.ident name) n = .ident name := rfl

/-- Generic heads retain their own type data before the call field decides erasure.
A step of the required-helper and owned-operation arguments proof. -/
theorem mapCalls_generic (call : Nat → Expr → Expr) (head : Expr) (types : List TypeRef) (n : Nat) :
    mapCalls call (.generic head types) n = .generic (mapCalls call head n) types := rfl

/-- A lambda's body folds at the parameter count above its enclosing depth.
Its consumer is the actual binder template relation. -/
theorem mapCalls_lambda (call : Nat → Expr → Expr) (ps : List Parameter) (body : Expr)
    (ty : Option TypeRef) (n : Nat) :
    mapCalls call (.lambda ps body ty) n = .lambda ps (mapCalls call body (n + ps.length)) ty := rfl

/-- Object property reconstruction retains names while folding values.
Its consumers are class and record term erasure. -/
theorem targetFold_properties (call : Nat → Expr → Expr) (names : List String)
    (values : List Expr) (n : Nat) :
    atDepth n (TargetFold.entries (callAlgebra call) (Record.properties names values)) =
      Record.properties names (values.map fun x => mapCalls call x n) := by
  induction names generalizing values with
  | nil => rfl
  | cons name names ih =>
    cases values with
    | nil => rfl
    | cons value values =>
      change .property name (mapCalls call value n) ::
          atDepth n (TargetFold.entries (callAlgebra call) (Record.properties names values)) =
        .property name (mapCalls call value n) ::
          Record.properties names (values.map fun x => mapCalls call x n)
      rw [ih]

/-- The normal record object's key form is scalar data; only property values fold.
Its consumers are class and record term erasure. -/
theorem mapCalls_objectProperties (call : Nat → Expr → Expr) (form : KeyForm)
    (names : List String) (values : List Expr) (n : Nat) :
    mapCalls call (.objectWith form (Record.properties names values)) n =
      .objectWith form (Record.properties names (values.map fun x => mapCalls call x n)) := by
  change Expr.objectWith form (atDepth n
    (TargetFold.entries (callAlgebra call) (Record.properties names values))) = _
  rw [targetFold_properties]

/-- A class construction folds its supplied values without changing the declaration data.
Its consumer is the record arm of pure-term erasure. -/
theorem mapCalls_writeClass (call : Nat → Expr → Expr) (tag : String)
    (names : List String) (values : List Expr) (n : Nat) :
    mapCalls call (Classes.writeClass tag names values) n =
      Classes.writeClass tag names (values.map fun x => mapCalls call x n) := by
  change Expr.new (.ident tag) [mapCalls call
      (.objectWith (Record.keyForm names) (Record.properties names values)) n] = _
  rw [mapCalls_objectProperties]
  rfl

/-- Byte metadata contains no operation call. Its consumer is record-term erasure. -/
theorem mapCalls_writeBytes (call : Nat → Expr → Expr) (bs : Effect4.Store.Bytes) (n : Nat) :
    mapCalls call (Metadata.writeBytes bs) n = Metadata.writeBytes bs := by
  simp only [Metadata.writeBytes, mapCalls_arr, List.map_map]
  rfl

/-- Natural metadata contains no operation call. Its consumer is record-term erasure. -/
theorem mapCalls_writeNat (call : Nat → Expr → Expr) (value n : Nat) :
    mapCalls call (Metadata.writeNat value) n = Metadata.writeNat value :=
  mapCalls_writeBytes call _ n

/-- Folding metadata through call reconstruction has the existing metadata algebra.
Its consumer is `mapCalls_writeValue`, a step of pure-term identity for typed-print erasure. -/
def metadataHom (call : Nat → Expr → Expr) (n : Nat) :
    Effect4.Store.ValHom Metadata.valueAlgebra := by
  refine' { f_val := fun v => mapCalls call (Metadata.writeValue v) n, .. }
  all_goals
    intros
    simp only [Metadata.writeValue, Effect4.Store.cata_val, Metadata.valueAlgebra,
      mapCalls_arr, List.map_cons, List.map_nil, mapCalls_writeNat, mapCalls_writeBytes,
      Effect4.Store.cata_pos_list_val_eq, List.map_map]
    rfl

/-- Every metadata value reconstructs unchanged by the call fold, by algebra agreement.
Its consumer is record-term identity, serving the proposed typed-print erasure claim (R8). -/
theorem mapCalls_writeValue (call : Nat → Expr → Expr) (v : Effect4.Store.Val) (n : Nat) :
    mapCalls call (Metadata.writeValue v) n = Metadata.writeValue v :=
  Effect4.Store.hom_eq_cata_val (metadataHom call n) v

/-- Type metadata retains every stored declaration under the call fold.
Its consumer is the record arm of pure-term erasure. -/
theorem mapCalls_writeTy (call : Nat → Expr → Expr) (ty : Ty) (n : Nat) :
    mapCalls call (Metadata.writeTy ty) n = Metadata.writeTy ty :=
  mapCalls_writeValue call _ n

/-- Head insertion commutes with appending the binder function, whenever insertion succeeds.
Its consumer is `printPerformAt_head`; method syntax remains a method before insertion. -/
theorem withFunction_headTypes {spelling : String} {types : List TypeRef}
    {call typedCall fn typed : Expr}
    (ht : withHeadTypes spelling types call = .ok typedCall)
    (hf : withFunction spelling fn typedCall = .ok typed) :
    ∃ plain, withFunction spelling fn call = .ok plain ∧
      withHeadTypes spelling types plain = .ok typed := by
  unfold withHeadTypes at ht
  split at ht
  · cases ht
    simp only [withFunction, Except.ok.injEq] at hf
    subst typed
    exact ⟨_, rfl, rfl⟩
  · cases ht
    simp only [withFunction, Except.ok.injEq] at hf
    subst typed
    exact ⟨_, rfl, rfl⟩
  · exact nomatch ht

/-- Successful nonempty insertion owns no operation or row-declared argument.
This discharges the ownership premise of the raw typed-print erasure claim (exact-codecs, R8). -/
theorem printPerformAt_owned_empty {n : Nat} {op : Op} {r : Term} {ty : Ty} {tys : List Ty}
    {typed : Expr}
    (hp : Templates.printPerformAt sig n op r (some (ty :: tys)) = .ok typed) :
    sig.typeArgsOf op = [] ∧ (sig.rowOf op).typeArgs = [] := by
  simp only [Templates.printPerformAt] at hp
  split at hp
  · rename_i eligible
    simp only [Bool.and_eq_true] at eligible
    obtain ⟨owned, declared⟩ := eligible
    exact ⟨List.nil_of_isEmpty owned, List.nil_of_isEmpty declared⟩
  · exact nomatch hp

/-- A successful nonempty annotation inserts one
nonempty target list into the ordinary complete call. This is the input to the row inverse,
serving the proposed typed-print erasure claim (exact-codecs, R8). -/
theorem printPerformAt_head {n : Nat} {op : Op} {r : Term} {ty : Ty} {tys : List Ty}
    {typed : Expr}
    (hp : Templates.printPerformAt sig n op r (some (ty :: tys)) = .ok typed) :
    ∃ plain target targets, printPerform sig n op r = .ok plain ∧
      withHeadTypes (sig.rowOf op).spelling (target :: targets) plain = .ok typed := by
  obtain ⟨hown, hdecl⟩ := printPerformAt_owned_empty hp
  simp only [Templates.printPerformAt, hown, hdecl, List.isEmpty_nil, Bool.and_self,
    ↓reduceIte] at hp
  cases hwrite : Classes.writeTys (ty :: tys) with
  | none =>
    rw [hwrite] at hp
    cases hb : sig.termOf op <;> rw [hb] at hp <;> exact nomatch hp
  | some types =>
    have hlength := Classes.writeTys_length hwrite
    cases types with
    | nil =>
      simp only [List.length_nil, List.length_cons] at hlength
      have impossible : False := by omega
      exact False.elim impossible
    | cons target targets =>
      rw [hwrite] at hp
      cases hb : sig.termOf op with
      | none =>
        rw [hb] at hp
        obtain ⟨plain, hplain, htyped⟩ := bind_eq_ok.mp hp
        exact ⟨plain, target, targets, by simp only [printPerform, hb, printCall, hown]; exact hplain,
          htyped⟩
      | some b =>
        rw [hb] at hp
        obtain ⟨typedCall, htypedCall, htyped⟩ := bind_eq_ok.mp hp
        obtain ⟨call, hcall, hhead⟩ := bind_eq_ok.mp htypedCall
        obtain ⟨plain, hplain, hfinal⟩ := withFunction_headTypes hhead htyped
        refine ⟨plain, target, targets, ?_, hfinal⟩
        simp only [printPerform, hb, printCall, hown, hcall]
        exact hplain

/-- A successful head insertion erases at the operation's complete readable call.
This is the leaf step of the proposed typed-print erasure claim (exact-codecs, R8).
Its consumer is the typed-printer template relation; it establishes no target execution. -/
theorem eraseRowJoin_withHeadTypes (hl : LawfulSpelling sig spell) {n : Nat} {op : Op}
    {r : Term} (hd : sig.dom op = true)
    (hreq : requestReadable (sig.rowOf op) n r = true) (hc : r.covers classes = true)
    (hu : r.unannotated = true)
    (htypes : typeArgsReadable (sig.rowOf op) (sig.typeArgsOf op) = true)
    (hterm : termReadable classes n (sig.rowOf op) ((sig.termOf op).map (·.term)) = true)
    (hown : sig.typeArgsOf op = []) (hdecl : (sig.rowOf op).typeArgs = [])
    {plain typed : Expr} (hp : printPerform sig n op r = .ok plain)
    {target : TypeRef} {targets : List TypeRef}
    (ht : withHeadTypes (sig.rowOf op).spelling (target :: targets) plain = .ok typed) :
    eraseRowJoin classes sig spell n typed = plain := by
  unfold eraseRowJoin
  simp only [splitHeadTypes_withHeadTypes ht,
    readPerform_printPerform hl hd hreq hc hu htypes hterm hp,
    hown, hdecl, List.isEmpty_nil, Bool.and_self, ↓reduceIte]

/-- The raw annotated row call erases to its ordinary complete call at the leaf.
This is the row step of the proposed typed-print erasure claim (exact-codecs, R8).
The template lift must additionally account for the fold of its request and binder children. -/
theorem eraseRowJoin_printPerformAt (hl : LawfulSpelling sig spell) {n : Nat} {op : Op}
    {r : Term} (hd : sig.dom op = true)
    (hreq : requestReadable (sig.rowOf op) n r = true) (hc : r.covers classes = true)
    (hu : r.unannotated = true)
    (htypes : typeArgsReadable (sig.rowOf op) (sig.typeArgsOf op) = true)
    (hterm : termReadable classes n (sig.rowOf op) ((sig.termOf op).map (·.term)) = true)
    {ty : Ty} {tys : List Ty} {typed : Expr}
    (hp : Templates.printPerformAt sig n op r (some (ty :: tys)) = .ok typed) :
    printPerform sig n op r = .ok (eraseRowJoin classes sig spell n typed) := by
  obtain ⟨hown, hdecl⟩ := printPerformAt_owned_empty hp
  obtain ⟨plain, target, targets, hplain, hhead⟩ := printPerformAt_head hp
  rw [eraseRowJoin_withHeadTypes hl hd hreq hc hu htypes hterm hown hdecl hplain hhead]
  exact hplain

/-- The read-back consumer of an erased raw successful-print equation.
Its consumer is the proposed structural connector; its hypotheses retain the existing
`Readable` and `LawfulSpelling` boundaries (exact-codecs, R8). -/
theorem readTyped_of_print_erasure (hl : LawfulSpelling sig spell) {n : Nat} {e : Eff Op}
    (hr : Readable classes sig n e = true) {x : Expr}
    (hp : print sig n e = .ok (eraseJoinArgs classes sig spell n x)) :
    readTyped classes sig spell n x = .ok e := by
  exact read_print hl hr hp

/-- The typed reader carries the ordinary reader's exactness at the erased input.
This is the exactness consumer of the proposed typed-print erasure claim (exact-codecs, R8).
It states no equality of raw target spellings and no target execution. -/
@[semantics "exact-codecs" (requirement := R8)]
theorem readTyped_exact (hl : LawfulSpelling sig spell) {n : Nat} {x : Expr} {e : Eff Op}
    (h : readTyped classes sig spell n x = .ok e) :
    print sig n e = .ok (eraseJoinArgs classes sig spell n x) := by
  exact read_exact hl h

end Effect4.Codegen

namespace Effect4.Codegen.EraseTermTypes

open TypeScript Effect4.Program

-- Placement: exact-codecs R8, raw-leaf steps of the full typed-print erasure connector.
-- Merge after the existing generic mapCalls transport lemmas in Laws/Codegen/PrintTyped.
-- Every statement below compares with the existing ordinary printer. No read restriction is added.

theorem eraseTerm_ident (n : Nat) (name : String) :
    eraseTerm n (.ident name) = .ident name := rfl

theorem eraseTerm_printLit (n : Nat) (value : Lit) :
    eraseTerm n (printLit value) = printLit value := by
  cases value <;> rfl

theorem eraseTerm_str (n : Nat) (value : String) : eraseTerm n (.str value) = .str value := rfl

theorem eraseTerm_call (n : Nat) (head : Expr) (values : List Expr) :
    eraseTerm n (.call head values) =
      callInverse n (.call (eraseTerm n head) (values.map (eraseTerm n))) :=
  mapCalls_call callInverse head values n

theorem eraseTerm_generic (n : Nat) (head : Expr) (types : List TypeRef) :
    eraseTerm n (.generic head types) = .generic (eraseTerm n head) types := rfl

theorem eraseTerm_lambda (n : Nat) (ps : List Parameter) (body : Expr) (ret : Option TypeRef) :
    eraseTerm n (.lambda ps body ret) = .lambda ps (eraseTerm (n + ps.length) body) ret := rfl

theorem eraseTerm_arr (n : Nat) (values : List Expr) :
    eraseTerm n (.arr values) = .arr (values.map (eraseTerm n)) := mapCalls_arr callInverse values n

theorem eraseTerm_objectProperties (n : Nat) (form : KeyForm) (names : List String) (values : List Expr) :
    eraseTerm n (.objectWith form (Record.properties names values)) =
      .objectWith form (Record.properties names (values.map (eraseTerm n))) :=
  mapCalls_objectProperties callInverse form names values n

theorem eraseTerm_writeClass (n : Nat) (tag : String) (names : List String) (values : List Expr) :
    eraseTerm n (Classes.writeClass tag names values) =
      Classes.writeClass tag names (values.map (eraseTerm n)) :=
  mapCalls_writeClass callInverse tag names values n

theorem eraseTerm_writeTy (n : Nat) (ty : Ty) : eraseTerm n (Metadata.writeTy ty) = Metadata.writeTy ty :=
  mapCalls_writeTy callInverse ty n

theorem eraseTerm_strings (n : Nat) (names : List String) :
    (names.map Expr.str).map (eraseTerm n) = names.map Expr.str := by
  induction names with
  | nil => rfl
  | cons name rest ih => simp only [List.map_cons, eraseTerm_str, ih]

theorem printTerm_not_lambda (n : Nat) (t : Term) (ps : List Parameter)
    (body : Expr) (ret : Option TypeRef) : printTerm n t ≠ .lambda ps body ret := by
  intro h
  cases t with
  | var _ => exact nomatch h
  | lit value => cases value <;> exact nomatch h
  | app _ _ => exact nomatch h
  | record fields names values =>
    simp only [printTerm] at h
    cases hc : Classes.classTag? fields names values with
    | some tag => rw [hc] at h; exact nomatch h
    | none =>
      rw [hc] at h
      simp only [Record.writeRecord] at h
      cases ht : Record.targetType fields names (printTerms n values) with
      | none => rw [ht] at h; exact nomatch h
      | some ty => rw [ht] at h; exact nomatch h
  | field _ _ _ => exact nomatch h
  | recordSet _ _ _ => exact nomatch h
  | tupleAt _ _ => exact nomatch h
  | fold stored _ _ _ =>
    simp only [printTerm, ListFold.write] at h
    cases stored <;> exact nomatch h

/-- An ordinary atom's children print to no lambda. Thus its bare call cannot impersonate
an inferred fold callback, even when its atom name is `fold`. -/
theorem callInverse_printedApp (n : Nat) (name : String) (args : Terms) :
    callInverse n (.call (.ident name) (printTerms n args)) =
      .call (.ident name) (printTerms n args) := by
  by_cases hname : name = "fold"
  · subst name
    cases args with
    | nil => simp only [printTerms, callInverse, eraseRecordJoin, eraseFoldJoin, ↓reduceIte, eraseCauseTermJoin]
    | cons first rest =>
      cases rest with
      | nil => simp only [printTerms, callInverse, eraseRecordJoin, eraseFoldJoin, ↓reduceIte, eraseCauseTermJoin]
      | cons second rest =>
        cases rest with
        | nil => simp only [printTerms, callInverse, eraseRecordJoin, eraseFoldJoin, ↓reduceIte, eraseCauseTermJoin]
        | cons third rest =>
          cases rest with
          | cons fourth tail =>
            simp only [printTerms, callInverse, eraseRecordJoin, eraseFoldJoin, ↓reduceIte, eraseCauseTermJoin]
          | nil =>
            have hnl := printTerm_not_lambda n third
            cases ht : printTerm n third <;>
              simp only [printTerms, ht, callInverse, eraseRecordJoin, eraseFoldJoin,
                eraseCauseTermJoin] <;> aesop
  · simp only [callInverse, eraseRecordJoin, eraseFoldJoin, hname, ↓reduceIte, eraseCauseTermJoin]

theorem eraseTerm_record (n : Nat) (fields : Record.Fields) (names : List String) (values : List Expr) :
    eraseTerm n (Record.writeRecord fields names values) =
      Record.writeRecord fields names (values.map (eraseTerm n)) := by
  have htarget : Record.targetType fields names (values.map (eraseTerm n)) =
      Record.targetType fields names values := by
    simp only [Record.targetType, List.length_map]
  cases ht : Record.targetType fields names values with
  | none =>
    simp only [Record.writeRecord, htarget, ht, eraseTerm_call, eraseTerm_generic,
      eraseTerm_ident, List.map_cons, List.map_nil, eraseTerm_writeTy, eraseTerm_arr,
      eraseTerm_strings]
    simp only [callInverse, eraseRecordJoin, eraseFoldJoin, ite_self, eraseCauseTermJoin]
  | some annotation =>
    simp only [Record.writeRecord, htarget, ht, eraseTerm_call, eraseTerm_generic,
      eraseTerm_ident, List.map_cons, List.map_nil, eraseTerm_writeTy, eraseTerm_objectProperties]
    simp only [callInverse, eraseRecordJoin, eraseFoldJoin, ite_self, eraseCauseTermJoin]

theorem eraseTerm_field (n : Nat) (optional : Bool) (key : String) (value : Expr) :
    eraseTerm n (Record.writeField optional key value) =
      Record.writeField optional key (eraseTerm n value) := by
  cases optional with
  | false =>
    simp only [Record.writeField, Bool.false_eq_true, ↓reduceIte, eraseTerm_call,
      eraseTerm_generic, eraseTerm_ident, List.map_cons, List.map_nil, eraseTerm_str]
    simp only [callInverse, eraseRecordJoin, eraseFoldJoin, ite_self, eraseCauseTermJoin]
  | true =>
    simp only [Record.writeField, ↓reduceIte, eraseTerm_call,
      eraseTerm_generic, eraseTerm_ident, List.map_cons, List.map_nil, eraseTerm_str]
    simp only [callInverse, eraseRecordJoin, eraseFoldJoin, ite_self, eraseCauseTermJoin]

theorem eraseTerm_set (n : Nat) (key : String) (receiver value : Expr) :
    eraseTerm n (Record.writeSet key receiver value) =
      Record.writeSet key (eraseTerm n receiver) (eraseTerm n value) := by
  simp only [Record.writeSet, eraseTerm_call, eraseTerm_generic,
    eraseTerm_ident, List.map_cons, List.map_nil, eraseTerm_str]
  simp only [callInverse, eraseRecordJoin, eraseFoldJoin, ite_self, eraseCauseTermJoin]

theorem eraseTerm_tupleAt (n index : Nat) (receiver : Expr) :
    eraseTerm n (Tuple.writeAt index receiver) = Tuple.writeAt index (eraseTerm n receiver) := by
  simp only [Tuple.writeAt, eraseTerm_call, eraseTerm_generic,
    eraseTerm_ident, List.map_cons, List.map_nil, eraseTerm_str]
  simp only [callInverse, eraseRecordJoin, eraseFoldJoin, ite_self, eraseCauseTermJoin]

/-- Raw stored-fold spellings keep their B, including the existing unsupported-type fallback.
The inverse touches neither a one-argument generic head nor an unannotated callback. -/
theorem eraseTerm_rawFold (n : Nat) (stored : Option TypeRef) (list init body : Expr) :
    eraseTerm n (ListFold.write n stored list init body) =
      ListFold.write n stored (eraseTerm n list) (eraseTerm n init) (eraseTerm (n + 2) body) := by
  cases stored with
  | none =>
    simp only [ListFold.write, Binders.write, eraseTerm_call, eraseTerm_ident,
      eraseTerm_lambda, Template.params, List.map_cons, List.map_nil,
      List.length_cons, List.length_nil, Nat.add_zero]
    simp only [callInverse, eraseRecordJoin, eraseFoldJoin, ↓reduceIte, eraseCauseTermJoin]
  | some stored =>
    simp only [ListFold.write, Binders.write, eraseTerm_call, eraseTerm_generic,
      eraseTerm_ident, eraseTerm_lambda, Template.params, List.map_cons, List.map_nil,
      List.length_cons, List.length_nil, Nat.add_zero]
    simp only [callInverse, eraseRecordJoin, eraseFoldJoin, ↓reduceIte, eraseCauseTermJoin]

end Effect4.Codegen.EraseTermTypes


/-!
Proposed typed-print erasure helpers: exact-codecs, R8.
The consumer is printArgs capture agreement in the erasure theorem.
Only recursive children advance the source child address.
Scalar argument positions still determine template hole numbers.
The helpers retain first-match lookup and the actual source argument positions.
-/


namespace Effect4.Codegen.Templates

open Effect4.Program

variable {Op : Type}

/-- The existing argument sort identifies recursive children. -/
def isChildArg {R : EffFam → Type} (arg : ArgF Op R) : Bool :=
  match argSortOf arg with
  | .child _ => true
  | _ => false

/-- Addressing changes a child's carrier, never its argument sort. -/
theorem argSortOf_atAddress (path : List Nat) (args : List (ArgF Op TCarrier)) (j : Nat) :
    (atAddress path args j).map argSortOf = args.map argSortOf := by
  induction args generalizing j with
  | nil => rfl
  | cons arg args ih =>
    cases arg <;> simp only [atAddress, List.map_cons, argSortOf, ih]

/-- The argument at position i uses the count of earlier recursive children as its address.
The singleton call is the existing argument transformation, including every scalar case. -/
theorem atAddress_getElem (path : List Nat) (args : List (ArgF Op TCarrier)) (j i : Nat) :
    (atAddress path args j)[i]? = args[i]?.bind (fun arg =>
      (atAddress path [arg] (j + (args.take i).countP isChildArg))[0]?) := by
  induction args generalizing j i with
  | nil => simp only [atAddress, List.getElem?_nil, Option.bind_none]
  | cons arg args ih =>
    cases i with
    | zero => cases arg <;> rfl
    | succ i =>
      cases arg with
      | child fam child =>
        simp only [atAddress, List.getElem?_cons_succ, List.take_succ_cons,
          List.countP_cons, isChildArg, argSortOf, ↓reduceIte]
        rw [ih]
        have offset : j + 1 + (args.take i).countP isChildArg =
            j + ((args.take i).countP isChildArg + 1) := by omega
        rw [offset]
      | term value =>
        simp only [atAddress, List.getElem?_cons_succ, List.take_succ_cons,
          List.countP_cons, isChildArg, argSortOf]
        exact ih j i
      | cause value =>
        simp only [atAddress, List.getElem?_cons_succ, List.take_succ_cons,
          List.countP_cons, isChildArg, argSortOf]
        exact ih j i
      | op value =>
        simp only [atAddress, List.getElem?_cons_succ, List.take_succ_cons,
          List.countP_cons, isChildArg, argSortOf]
        exact ih j i
      | nat value =>
        simp only [atAddress, List.getElem?_cons_succ, List.take_succ_cons,
          List.countP_cons, isChildArg, argSortOf]
        exact ih j i
      | mode value =>
        simp only [atAddress, List.getElem?_cons_succ, List.take_succ_cons,
          List.countP_cons, isChildArg, argSortOf]
        exact ih j i
      | bool value =>
        simp only [atAddress, List.getElem?_cons_succ, List.take_succ_cons,
          List.countP_cons, isChildArg, argSortOf]
        exact ih j i
      | key value =>
        simp only [atAddress, List.getElem?_cons_succ, List.take_succ_cons,
          List.countP_cons, isChildArg, argSortOf]
        exact ih j i
      | decision value =>
        simp only [atAddress, List.getElem?_cons_succ, List.take_succ_cons,
          List.countP_cons, isChildArg, argSortOf]
        exact ih j i
      | optTy value =>
        simp only [atAddress, List.getElem?_cons_succ, List.take_succ_cons,
          List.countP_cons, isChildArg, argSortOf]
        exact ih j i
      | forkOptions value =>
        simp only [atAddress, List.getElem?_cons_succ, List.take_succ_cons,
          List.countP_cons, isChildArg, argSortOf]
        exact ih j i
      | optTerm value =>
        simp only [atAddress, List.getElem?_cons_succ, List.take_succ_cons,
          List.countP_cons, isChildArg, argSortOf]
        exact ih j i
      | lit value =>
        simp only [atAddress, List.getElem?_cons_succ, List.take_succ_cons,
          List.countP_cons, isChildArg, argSortOf]
        exact ih j i
      | path value =>
        simp only [atAddress, List.getElem?_cons_succ, List.take_succ_cons,
          List.countP_cons, isChildArg, argSortOf]
        exact ih j i

/-- A captured child receives its parent's address followed by its child position. -/
theorem atAddress_getElem_child (path : List Nat) (args : List (ArgF Op TCarrier))
    (j i : Nat) (fam : EffFam) (child : TCarrier fam)
    (harg : args[i]? = some (.child fam child)) :
    (atAddress path args j)[i]? =
      some (.child fam (child (path ++ [j + (args.take i).countP isChildArg]))) := by
  rw [atAddress_getElem, harg]
  rfl

end Effect4.Codegen.Templates



/-!
Proposed helper of typed-print erasure: exact-codecs, R8.
A matched capture must identify an actual source argument.
The printArgs erasure bridge consumes this inverse of the existing lookup law.
The helper serves the capture reconstruction step of typed-print erasure.
-/


namespace Effect4.Codegen.Templates

open Effect4.Program Effect4.Codegen.Template

variable {Op : Type}

/-- A captured argument comes from its source position, at the row's actual binder depth.
The consumer is the printArgs erasure bridge of typed-print erasure (exact-codecs, R8). -/
theorem printArgs_lookup_some {sig : Signature Op} {fam : EffFam} {n : Nat} {out : RowOut} :
    ∀ (args : List (ArgF Op Carrier)) (i : Nat) (τ : Subst),
      printArgs sig fam n out args i = .ok τ →
      ∀ (j : Nat) (capture : Arg), lookup τ j = some capture →
      ∃ (k : Nat) (arg : ArgF Op Carrier), j = i + k ∧ args[k]? = some arg ∧
        printArg sig (argDepth fam (argSortOf arg) n (out.levelAt j)) arg = .ok (some capture)
  | [], i, τ, printed, j, capture, found => by
    simp only [printArgs, Except.ok.injEq] at printed
    subst τ
    simp only [lookup, List.find?_nil, Option.map_none] at found
    cases found
  | arg :: args, i, τ, printed, j, capture, found => by
    simp only [printArgs, bind_eq_ok] at printed
    obtain ⟨value, head, rest, tail, assembled⟩ := printed
    cases value with
    | none =>
      cases assembled
      obtain ⟨k, item, index, member, printed⟩ :=
        printArgs_lookup_some args (i + 1) _ tail j capture found
      exact ⟨k + 1, item, by omega, member, printed⟩
    | some value =>
      cases assembled
      by_cases eq : i = j
      · subst j
        rw [lookup_cons_self] at found
        cases found
        exact ⟨0, arg, by omega, rfl, head⟩
      · rw [lookup_cons_ne i j value rest eq] at found
        obtain ⟨k, item, index, member, printed⟩ :=
          printArgs_lookup_some args (i + 1) rest tail j capture found
        exact ⟨k + 1, item, by omega, member, printed⟩

end Effect4.Codegen.Templates

/-!
Proposed helpers of typed-print erasure: exact-codecs, R8.
The generic row step consumes these first-match separation laws.
Each theorem retains the existing table's rowsApart premises.
The helpers serve first-match separation in typed-print erasure.
-/

namespace Effect4.Codegen
open TypeScript Effect4.Program Template Templates
variable {Op : Type} {classes : Classes.Classes} {sig : Signature Op}
  {spell : String → List String → Option Op}
  {fam : EffFam} {n : Nat} {x : Expr}
  {child : EffFam → Nat → (y : Expr) → sizeOf y < sizeOf x → Expr}
  {children : EffFam → Nat → (ys : List Expr) → sizeOf ys < sizeOf x → List Expr}
  {block : Nat → (ss : List TypeScript.Stmt) → sizeOf ss < sizeOf x → List TypeScript.Stmt}
  {same : (fam' : EffFam) → famRank fam' < famRank fam → Nat → Option Expr}

theorem eraseExprRow_none_of_fam {row : Templates.Row} (h : row.fam ≠ fam) :
    eraseExprRow classes sig spell fam n x row child children block same = none := by
  unfold eraseExprRow; simp only [h, ↓reduceIte]

theorem eraseExprRow_none_of_refuse {row : Templates.Row} {name : String} (h : row.out = .refuse name) :
    eraseExprRow classes sig spell fam n x row child children block same = none := by
  unfold eraseExprRow; aesop

theorem eraseExprRow_none_of_stmt {row : Templates.Row} {t : StmtTpl} (h : row.out = .stmt t) :
    eraseExprRow classes sig spell fam n x row child children block same = none := by
  unfold eraseExprRow; aesop

theorem eraseExprRow_none_of_nomatch {row : Templates.Row} {t : Tpl} (hout : row.out = .tpl t)
    (hm : matchT n t x = none) :
    eraseExprRow classes sig spell fam n x row child children block same = none := by
  unfold eraseExprRow; aesop

/-- A transparent row whose lower family reads nothing reads nothing. -/
theorem eraseExprRow_none_of_same {row : Templates.Row} {i : Nat} (hout : row.out = .tpl (.hole i))
    {fam' : EffFam} (hsorts : argSorts row.fam row.ctor = some [.child fam'])
    (hsame : ∀ hk d, same fam' hk d = none) :
    eraseExprRow classes sig spell fam n x row child children block same = none := by
  unfold eraseExprRow
  aesop (add norm simp [Tpl.rigid, hsame])

section Earlier

variable {rj : Templates.Row} {row : Templates.Row} (hap : rowsApart rj row = true)
include hap

/-- Before a rigid printing row. -/
theorem erase_earlier_none_rigid {t : Tpl} (hout : row.out = .tpl t) (hrigid : t.rigid = true)
    {sorts : List ArgSort} (hsorts : argSorts row.fam row.ctor = some sorts) {τ : Subst}
    (hinst : inst n τ t = some x)
    (hnode : ∀ i y, childHole sorts i = true → i ∈ holes t → lookup τ i = some (.expr y) →
      nodeLike y = true) :
    eraseExprRow classes sig spell fam n x rj child children block same = none := by
  unfold rowsApart at hap
  rw [hout] at hap
  simp only [hrigid, ↓reduceIte, hsorts] at hap
  split at hap
  · rename_i name h; exact eraseExprRow_none_of_refuse h
  · rename_i st h; exact eraseExprRow_none_of_stmt h
  · cases hap
  · rename_i t' h
    simp only [Bool.and_eq_true] at hap
    exact eraseExprRow_none_of_nomatch h (match_apart n τ sorts t' t x hap.2 hinst hnode)

/-- Before the transparent row that hands to the action family: the image is an action's. -/
theorem erase_earlier_none_action {i : Nat} (hout : row.out = .tpl (.hole i))
    (hsorts : argSorts row.fam row.ctor = some [.child .action]) {h : String}
    (hx : exprHead? x = some h) (hact : h ∈ actionHeads) :
    eraseExprRow classes sig spell fam n x rj child children block same = none := by
  unfold rowsApart at hap
  rw [hout] at hap
  simp only [Tpl.rigid, Bool.false_eq_true, ↓reduceIte, hsorts] at hap
  split at hap
  · rename_i name h; exact eraseExprRow_none_of_refuse h
  · rename_i st h; exact eraseExprRow_none_of_stmt h
  · cases hap
  · rename_i t' h'
    simp only [Bool.and_eq_true, Option.any_eq_true] at hap
    obtain ⟨_, h'', hh, hnot⟩ := hap
    refine eraseExprRow_none_of_nomatch h' ?_
    cases hm : matchT n t' x with
    | none => rfl
    | some σ =>
      have := head_of_match n t' x σ hm hh
      rw [hx, Option.some.injEq] at this
      subst this
      simp only [List.contains_eq_mem, hact, decide_true, Bool.not_true, Bool.false_eq_true] at hnot

/-- Before the transparent row that reads a name: the image is an identifier. -/
theorem erase_earlier_none_path {i : Nat} (hout : row.out = .tpl (.hole i))
    (hsorts : argSorts row.fam row.ctor = some [.path]) {s : String} (hx : x = .ident s) :
    eraseExprRow classes sig spell fam n x rj child children block same = none := by
  unfold rowsApart at hap
  rw [hout] at hap
  simp only [Tpl.rigid, Bool.false_eq_true, ↓reduceIte, hsorts] at hap
  split at hap
  · rename_i name h; exact eraseExprRow_none_of_refuse h
  · rename_i st h; exact eraseExprRow_none_of_stmt h
  · cases hap
  · rename_i t' h'
    simp only [Bool.and_eq_true] at hap
    subst hx
    exact eraseExprRow_none_of_nomatch h' (matchT_ident_none n t' s hap.2)

/-- Reserved heads cannot claim an operation call, before its row erases inserted arguments.
The consumer supplies the printed call's head separation; no erasure equality is assumed. -/
theorem erase_earlier_none_rowCall (hrow : row.out = .rowCall)
    (hreserved : ∀ (t : Tpl) (h : String), t.head? = some h → h ∈ reserved →
      matchT n t x = none)
    (hsame : ∀ hk d, same .action hk d = none) :
    eraseExprRow classes sig spell fam n x rj child children block same = none := by
  unfold rowsApart at hap
  rw [hrow] at hap
  simp only at hap
  split at hap
  · rename_i name h; exact eraseExprRow_none_of_refuse h
  · rename_i st h; exact eraseExprRow_none_of_stmt h
  · cases hap
  · rename_i t' h'
    simp only [Bool.or_eq_true, Bool.and_eq_true, Option.any_eq_true, Bool.not_eq_true',
      beq_iff_eq] at hap
    rcases hap with ⟨_, h, hh, hres⟩ | ⟨hnr, hsorts⟩
    · exact eraseExprRow_none_of_nomatch h'
        (hreserved t' h hh (List.mem_of_elem_eq_true hres))
    · cases t' with
      | hole i => exact eraseExprRow_none_of_same h' hsorts hsame
      | _ => cases hnr

end Earlier

end Effect4.Codegen


namespace Effect4.Codegen.EraseTermTypes

open TypeScript Effect4.Program

-- Keep the already checked write transports through eraseTerm_rawFold before this section.
-- Replace the final mutual identities by homomorphism agreement below.

theorem eraseRecordJoin_hasCall (x : Expr) (input : ∃ head args, x = .call head args) :
    ∃ head args, eraseRecordJoin x = .call head args := by
  fun_cases eraseRecordJoin x <;> aesop

theorem eraseRecordJoin_call (head : Expr) (args : List Expr) :
    ∃ head' args', eraseRecordJoin (.call head args) = .call head' args' :=
  eraseRecordJoin_hasCall (.call head args) ⟨head, args, rfl⟩

theorem eraseFoldJoin_hasCall (n : Nat) (x : Expr) (input : ∃ head args, x = .call head args) :
    ∃ head args, eraseFoldJoin n x = .call head args := by
  fun_cases eraseFoldJoin n x <;> aesop (add norm simp [ListFold.write])

theorem eraseFoldJoin_call (n : Nat) (head : Expr) (args : List Expr) :
    ∃ head' args', eraseFoldJoin n (.call head args) = .call head' args' :=
  eraseFoldJoin_hasCall n (.call head args) ⟨head, args, rfl⟩

theorem eraseCauseTermJoin_hasCall (x : Expr) (input : ∃ head args, x = .call head args) :
    ∃ head args, eraseCauseTermJoin x = .call head args := by
  fun_cases eraseCauseTermJoin x <;> aesop

theorem eraseCauseTermJoin_call (head : Expr) (args : List Expr) :
    ∃ head' args', eraseCauseTermJoin (.call head args) = .call head' args' :=
  eraseCauseTermJoin_hasCall (.call head args) ⟨head, args, rfl⟩

theorem callInverse_call (n : Nat) (head : Expr) (args : List Expr) :
    ∃ head' args', callInverse n (.call head args) = .call head' args' := by
  obtain ⟨firstHead, firstArgs, hfirst⟩ := eraseRecordJoin_call head args
  obtain ⟨secondHead, secondArgs, hsecond⟩ := eraseFoldJoin_call n firstHead firstArgs
  obtain ⟨lastHead, lastArgs, hlast⟩ := eraseCauseTermJoin_call secondHead secondArgs
  exact ⟨lastHead, lastArgs, by rw [callInverse, hfirst, hsecond, hlast]⟩

/-- The local inverse always returns a call from a call, even on syntax outside the print image.
This supports only the atom hom field, without assuming the raw identity it serves. -/
theorem eraseTerm_call_not_lambda (n : Nat) (head : Expr) (args : List Expr)
    (ps : List Parameter) (body : Expr) (ret : Option TypeRef) :
    eraseTerm n (.call head args) ≠ .lambda ps body ret := by
  rw [eraseTerm_call]
  obtain ⟨head', args', h⟩ := callInverse_call n (eraseTerm n head) (args.map (eraseTerm n))
  rw [h]
  intro h
  exact nomatch h

theorem eraseTerm_printTerm_not_lambda (n : Nat) (t : Term) (ps : List Parameter)
    (body : Expr) (ret : Option TypeRef) : eraseTerm n (printTerm n t) ≠ .lambda ps body ret := by
  cases t with
  | var _ => intro h; exact nomatch h
  | lit value => rw [printTerm, eraseTerm_printLit]; cases value <;> intro h <;> exact nomatch h
  | app name args => exact eraseTerm_call_not_lambda n (.ident name) (printTerms n args) ps body ret
  | record fields names values =>
    simp only [printTerm]
    cases hc : Classes.classTag? fields names values with
    | some tag => rw [eraseTerm_writeClass]; intro h; exact nomatch h
    | none =>
      rw [eraseTerm_record]
      simp only [Record.writeRecord]
      cases ht : Record.targetType fields names ((printTerms n values).map (eraseTerm n)) with
      | none => intro h; exact nomatch h
      | some ty => intro h; exact nomatch h
  | field _ _ _ =>
    simp only [printTerm, Record.writeField]
    exact eraseTerm_call_not_lambda n _ _ ps body ret
  | recordSet _ _ _ => exact eraseTerm_call_not_lambda n _ _ ps body ret
  | tupleAt _ _ => exact eraseTerm_call_not_lambda n _ _ ps body ret
  | fold stored _ _ _ =>
    simp only [printTerm, ListFold.write]
    cases stored <;> exact eraseTerm_call_not_lambda n _ _ ps body ret

theorem callInverse_erasedApp (n : Nat) (name : String) (args : Terms) :
    callInverse n (.call (.ident name) ((printTerms n args).map (eraseTerm n))) =
      .call (.ident name) ((printTerms n args).map (eraseTerm n)) := by
  by_cases hname : name = "fold"
  · subst name
    cases args with
    | nil => simp only [printTerms, List.map_nil, callInverse, eraseRecordJoin, eraseFoldJoin, ↓reduceIte, eraseCauseTermJoin]
    | cons first rest =>
      cases rest with
      | nil => simp only [printTerms, List.map_cons, List.map_nil, callInverse, eraseRecordJoin, eraseFoldJoin, ↓reduceIte, eraseCauseTermJoin]
      | cons second rest =>
        cases rest with
        | nil => simp only [printTerms, List.map_cons, List.map_nil, callInverse, eraseRecordJoin, eraseFoldJoin, ↓reduceIte, eraseCauseTermJoin]
        | cons third rest =>
          cases rest with
          | cons fourth tail => simp only [printTerms, List.map_cons, callInverse, eraseRecordJoin, eraseFoldJoin, ↓reduceIte, eraseCauseTermJoin]
          | nil =>
            have hnl := eraseTerm_printTerm_not_lambda n third
            cases ht : eraseTerm n (printTerm n third) <;>
              simp only [printTerms, List.map_cons, List.map_nil, ht, callInverse,
                eraseRecordJoin, eraseFoldJoin, ↓reduceIte, eraseCauseTermJoin]
            aesop
  · simp only [callInverse, eraseRecordJoin, eraseFoldJoin, hname, ↓reduceIte, eraseCauseTermJoin]

def RawPrintCarrier : TermFam → Type
  | .term => Term × (Nat → Expr)
  | .terms => Terms × (Nat → List Expr)

/-- The original syntax component selects the existing class form; both prints use one algebra. -/
def rawPrintAlg : TermAlgebra RawPrintCarrier where
  term_var index := (.var index, fun _ => .ident (Var.name index))
  term_lit value := (.lit value, fun _ => printLit value)
  term_app name args := (.app name args.1, fun n => .call (.ident name) (args.2 n))
  term_record fields names values := (.record fields names values.1, fun n =>
    match Classes.classTag? fields names values.1 with
    | some tag => Classes.writeClass tag names.tail (values.2 n).tail
    | none => Record.writeRecord fields names (values.2 n))
  term_field mode receiver key := (.field mode receiver.1 key, fun n =>
    Record.writeField (decide (mode = .optional)) key (receiver.2 n))
  term_recordSet receiver key value := (.recordSet receiver.1 key value.1, fun n =>
    Record.writeSet key (receiver.2 n) (value.2 n))
  term_tupleAt receiver index := (.tupleAt receiver.1 index, fun n => Tuple.writeAt index (receiver.2 n))
  term_fold stored list init body := (.fold stored list.1 init.1 body.1, fun n =>
    ListFold.write n (stored.map ListFold.typeArg) (list.2 n) (init.2 n) (body.2 (n + 2)))
  terms_nil := (.nil, fun _ => [])
  terms_cons first rest := (.cons first.1 rest.1, fun n => first.2 n :: rest.2 n)

def rawPrintHom : TermHom rawPrintAlg where
  f_term t := (t, fun n => printTerm n t)
  f_terms ts := (ts, fun n => printTerms n ts)
  h_term_var _ := rfl
  h_term_lit _ := rfl
  h_term_app _ _ := rfl
  h_term_record _ _ _ := rfl
  h_term_field _ _ _ := rfl
  h_term_recordSet _ _ _ := rfl
  h_term_tupleAt _ _ := rfl
  h_term_fold _ _ _ _ := rfl
  h_terms_nil := rfl
  h_terms_cons _ _ := rfl

def erasedPrintHom : TermHom rawPrintAlg where
  f_term t := (t, fun n => eraseTerm n (printTerm n t))
  f_terms ts := (ts, fun n => (printTerms n ts).map (eraseTerm n))
  h_term_var _ := rfl
  h_term_lit value := by
    apply Prod.ext
    · rfl
    · funext n; exact eraseTerm_printLit n value
  h_term_app name args := by
    apply Prod.ext
    · rfl
    · funext n
      simp only [printTerm, eraseTerm_call, eraseTerm_ident]
      exact callInverse_erasedApp n name args
  h_term_record fields names values := by
    apply Prod.ext
    · rfl
    · funext n
      change eraseTerm n (printTerm n (.record fields names values)) = _
      simp only [printTerm, rawPrintAlg]
      cases hc : Classes.classTag? fields names values with
      | some tag => simp only [eraseTerm_writeClass, List.map_tail]
      | none => exact eraseTerm_record n fields names (printTerms n values)
  h_term_field mode receiver key := by
    apply Prod.ext
    · rfl
    · funext n; exact eraseTerm_field n (decide (mode = .optional)) key (printTerm n receiver)
  h_term_recordSet receiver key value := by
    apply Prod.ext
    · rfl
    · funext n; exact eraseTerm_set n key (printTerm n receiver) (printTerm n value)
  h_term_tupleAt receiver index := by
    apply Prod.ext
    · rfl
    · funext n; exact eraseTerm_tupleAt n index (printTerm n receiver)
  h_term_fold stored list init body := by
    apply Prod.ext
    · rfl
    · funext n
      exact eraseTerm_rawFold n (stored.map ListFold.typeArg)
        (printTerm n list) (printTerm n init) (printTerm (n + 2) body)
  h_terms_nil := rfl
  h_terms_cons first rest := rfl

/-- Two homomorphisms into the existing print algebra agree by the generated fold law. -/
theorem eraseTerm_printTerm_identity (n : Nat) (t : Term) :
    eraseTerm n (printTerm n t) = printTerm n t := by
  have h := (hom_eq_cata_term erasedPrintHom t).trans (hom_eq_cata_term rawPrintHom t).symm
  exact congrArg (fun value => value.2 n) h

theorem eraseTerms_printTerms_identity (n : Nat) (ts : Terms) :
    (printTerms n ts).map (eraseTerm n) = printTerms n ts := by
  have h := (hom_eq_cata_terms erasedPrintHom ts).trans (hom_eq_cata_terms rawPrintHom ts).symm
  exact congrArg (fun value => value.2 n) h

def rawCauseAlg : CauseTermAlgebra (fun _ => Nat → Expr) where
  cause_fail t n := .call (.ident "Cause.fail") [printTerm n t]
  cause_die t n := .call (.ident "Cause.die") [printTerm n t]
  cause_interrupt who n := .call (.ident "Cause.interrupt") (who.toList.map (printTerm n))
  cause_both left right n := .call (.ident "Cause.combine") [left n, right n]

def rawCauseHom : CauseTermHom rawCauseAlg where
  f_cause c := fun n => printCause n c
  h_cause_fail _ := rfl
  h_cause_die _ := rfl
  h_cause_interrupt who := by cases who <;> rfl
  h_cause_both _ _ := rfl

def erasedCauseHom : CauseTermHom rawCauseAlg where
  f_cause c := fun n => eraseCause n (printCause n c)
  h_cause_fail t := by
    funext n
    simp only [eraseCause, printCause, rawCauseAlg, eraseTerm_call, eraseTerm_ident,
      List.map_cons, List.map_nil, eraseTerm_printTerm_identity]
    simp only [callInverse, eraseRecordJoin, eraseFoldJoin, ite_self, eraseCauseTermJoin]
  h_cause_die t := by
    funext n
    simp only [eraseCause, printCause, rawCauseAlg, eraseTerm_call, eraseTerm_ident,
      List.map_cons, List.map_nil, eraseTerm_printTerm_identity]
    simp only [callInverse, eraseRecordJoin, eraseFoldJoin, ite_self, eraseCauseTermJoin]
  h_cause_interrupt who := by
    funext n
    cases who <;>
      simp only [eraseCause, printCause, rawCauseAlg, Option.toList_none, Option.toList_some,
        List.map_cons, List.map_nil, eraseTerm_call, eraseTerm_ident, eraseTerm_printTerm_identity] <;>
      simp only [callInverse, eraseRecordJoin, eraseFoldJoin, ite_self, eraseCauseTermJoin]
  h_cause_both left right := by
    funext n
    simp only [eraseCause, printCause, rawCauseAlg, eraseTerm_call, eraseTerm_ident,
      List.map_cons, List.map_nil]
    simp only [callInverse, eraseRecordJoin, eraseFoldJoin, ite_self, eraseCauseTermJoin]

/-- Raw cause printing and its erased form agree by the generated cause fold law. -/
theorem eraseCause_printCause_identity (n : Nat) (c : CauseTerm) :
    eraseCause n (printCause n c) = printCause n c := by
  have h := (hom_eq_cata_cause erasedCauseHom c).trans (hom_eq_cata_cause rawCauseHom c).symm
  exact congrArg (fun value => value n) h

end Effect4.Codegen.EraseTermTypes



namespace Effect4.Codegen.Templates

open Effect4.Program Effect4.Codegen.Template

variable {Op : Type}

/-- Argument printing transports capture values without changing their source indices.
This serves typed-print erasure (exact-codecs, R8); the consumer supplies actual leaf and child laws. -/
theorem printArgs_transport {sig : Signature Op} {fam : EffFam} {n : Nat} {out : RowOut}
    (f : Nat → Arg → Arg) :
    ∀ (typed plain : List (ArgF Op Carrier)) (i : Nat), typed.length = plain.length →
      (∀ k ta pa, typed[k]? = some ta → plain[k]? = some pa → ∀ value,
        printArg sig (argDepth fam (argSortOf ta) n (out.levelAt (i + k))) ta = .ok value →
        printArg sig (argDepth fam (argSortOf pa) n (out.levelAt (i + k))) pa =
          .ok (value.map (f (i + k)))) →
      ∀ τ, printArgs sig fam n out typed i = .ok τ →
      ∃ υ, printArgs sig fam n out plain i = .ok υ ∧
        ∀ j, lookup υ j = (lookup τ j).map (f j)
  | [], [], i, _, _, τ, printed => by
    simp only [printArgs, Except.ok.injEq] at printed
    subst τ
    exact ⟨[], rfl, fun _ => rfl⟩
  | [], _ :: _, _, lengths, _, _, _ => by cases lengths
  | _ :: _, [], _, lengths, _, _, _ => by cases lengths
  | ta :: typed, pa :: plain, i, lengths, transport, τ, printed => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at lengths
    simp only [printArgs, bind_eq_ok] at printed
    obtain ⟨value, head, rest, tail, assembled⟩ := printed
    have head' := transport 0 ta pa rfl rfl value (by simpa only [Nat.add_zero] using head)
    simp only [Nat.add_zero] at head'
    have tails : ∀ k ta pa, typed[k]? = some ta → plain[k]? = some pa → ∀ value,
        printArg sig (argDepth fam (argSortOf ta) n (out.levelAt (i + 1 + k))) ta = .ok value →
        printArg sig (argDepth fam (argSortOf pa) n (out.levelAt (i + 1 + k))) pa =
          .ok (value.map (f (i + 1 + k))) := by
      intro k ta pa ht hp value hv
      have offset : i + (k + 1) = i + 1 + k := by omega
      simpa only [List.getElem?_cons_succ, offset] using
        transport (k + 1) ta pa ht hp value (by simpa only [offset] using hv)
    obtain ⟨υ, tail', lookup'⟩ := printArgs_transport f typed plain (i + 1) lengths tails rest tail
    cases value with
    | none =>
      cases assembled
      refine ⟨υ, ?_, lookup'⟩
      simp only [printArgs, head', Option.map_none, tail', ok_bind]
    | some a =>
      cases assembled
      refine ⟨(i, f i a) :: υ, ?_, ?_⟩
      · simp only [printArgs, head', Option.map_some, tail', ok_bind]
      · intro j
        by_cases eq : i = j
        · subst j
          simp only [lookup_cons_self, Option.map_some]
        · rw [lookup_cons_ne i j (f i a) υ eq, lookup_cons_ne i j a rest eq]
          exact lookup' j

end Effect4.Codegen.Templates


namespace Effect4.Codegen

open TypeScript Effect4.Program Template Templates

/-- The existing matched substitution chooses the capture at a template hole.
This adapter supplies argument transport without introducing a second program representation. -/
def eraseCaptureValue (row : Templates.Row) (sorts : List ArgSort) (n : Nat) (σ : Subst)
    (child : EffFam → Nat → (y : Expr) → (i : Nat) → (i, .expr y) ∈ σ → Expr)
    (children : EffFam → Nat → (ys : List Expr) → (i : Nat) → (i, .exprs ys) ∈ σ → List Expr)
    (block : Nat → (ss : List TypeScript.Stmt) → (i : Nat) → (i, .stmts ss) ∈ σ → List TypeScript.Stmt)
    (i : Nat) (fallback : Arg) : Arg :=
  if row.out.holes.contains i then
    match captured σ i with
    | some ⟨value, member⟩ =>
      eraseCapture row sorts n σ child children block ⟨(i, value), member⟩
    | none => fallback
  else fallback

/-- At a matched hole the adapter is the production capture transform.
This serves the argument bridge of typed-print erasure (exact-codecs, R8). -/
theorem eraseCaptureValue_at (row : Templates.Row) (sorts : List ArgSort) (n : Nat) (σ : Subst)
    (child : EffFam → Nat → (y : Expr) → (i : Nat) → (i, .expr y) ∈ σ → Expr)
    (children : EffFam → Nat → (ys : List Expr) → (i : Nat) → (i, .exprs ys) ∈ σ → List Expr)
    (block : Nat → (ss : List TypeScript.Stmt) → (i : Nat) → (i, .stmts ss) ∈ σ → List TypeScript.Stmt)
    {i : Nat} {a : Arg} (hole : i ∈ row.out.holes) (found : lookup σ i = some a)
    (member : (i, a) ∈ σ) :
    eraseCaptureValue row sorts n σ child children block i a =
      eraseCapture row sorts n σ child children block ⟨(i, a), member⟩ := by
  obtain ⟨member', capture⟩ := captured_of_lookup σ i a found
  unfold eraseCaptureValue
  simp only [List.contains_eq_mem, hole, decide_true, ↓reduceIte, capture]

end Effect4.Codegen




namespace Effect4.Codegen

open TypeScript Effect4.Program Template Templates

variable {Op : Type}

/-- A printed scalar capture keeps the ordinary leaf at its actual template depth.
This is the leaf step of typed-print erasure (exact-codecs, R8), consumed by argument transport. -/
theorem eraseCapture_printLeaf (sig : Signature Op) (row : Templates.Row)
    (sorts : List ArgSort) (n : Nat) (σ : Subst)
    (child : EffFam → Nat → (y : Expr) → (i : Nat) → (i, .expr y) ∈ σ → Expr)
    (children : EffFam → Nat → (ys : List Expr) → (i : Nat) → (i, .exprs ys) ∈ σ → List Expr)
    (block : Nat → (ss : List TypeScript.Stmt) → (i : Nat) → (i, .stmts ss) ∈ σ → List TypeScript.Stmt)
    (i : Nat) (source : ArgF Op (EffSelfCarrier Op))
    (leaf : ∀ fam value, source ≠ .child fam value)
    (sort : sorts[i]? = some (argSortOf source))
    (capture : Arg) (member : (i, capture) ∈ σ)
    (printed : printArg sig (argDepth row.fam (argSortOf source) n (row.out.levelAt i))
      (ArgF.fold (printAlg sig) source) = .ok (some capture)) :
    eraseCapture row sorts n σ child children block ⟨(i, capture), member⟩ = capture := by
  cases source with
  | child fam value => exact False.elim (leaf fam value rfl)
  | term value =>
    simp only [ArgF.fold, printArg, Except.ok.injEq, Option.some.injEq] at printed
    subst capture
    simp only [eraseCapture, sort, argSortOf, Option.getD_some,
      EraseTermTypes.eraseTerm_printTerm_identity]
  | cause value =>
    simp only [ArgF.fold, printArg, Except.ok.injEq, Option.some.injEq] at printed
    subst capture
    simp only [eraseCapture, sort, argSortOf, Option.getD_some,
      EraseTermTypes.eraseCause_printCause_identity]
  | optTerm value =>
    cases value with
    | none => cases printed
    | some value =>
      simp only [ArgF.fold, printArg, Except.ok.injEq, Option.some.injEq] at printed
      subst capture
      simp only [eraseCapture, sort, argSortOf, Option.getD_some,
        EraseTermTypes.eraseTerm_printTerm_identity]
  | op value => cases printed
  | mode value => cases printed
  | bool value => cases printed
  | nat value => cases printed; rfl
  | key value =>
    simp only [ArgF.fold, printArg, bind_eq_ok] at printed
    obtain ⟨key, keyPrinted, eq⟩ := printed
    cases eq
    simp only [eraseCapture, sort, argSortOf]
  | decision value =>
    cases value <;> cases printed <;> simp only [eraseCapture, sort, argSortOf]
  | optTy value =>
    cases value with
    | none => cases printed
    | some value =>
      simp only [ArgF.fold, printArg] at printed
      split at printed
      · cases printed; rfl
      · cases printed
  | forkOptions value =>
    cases printed
    simp only [eraseCapture, sort, argSortOf]
  | lit value =>
    cases printed
    simp only [eraseCapture, sort, argSortOf]
  | path value =>
    cases printed
    simp only [eraseCapture, sort, argSortOf]

end Effect4.Codegen


/-!
Placement: exact-codecs, R8, the row-child step of raw typed-print erasure.
Consumer: eraseRowJoin_printPerformAt after proper request and binder normalization.
Reach: existing row spellings and printRow, under the ordinary term identity helper.
The term premise is a helper dependency, not a new program or spelling restriction.
This file states no host result and adds no global signature restriction.
-/


namespace Effect4.Codegen

open TypeScript Effect4.Program

variable (fixed : ∀ d t, EraseTermTypes.eraseTerm d (printTerm d t) = printTerm d t)

theorem eraseTerm_trailing (n : Nat) (names : List String) :
    (names.map Expr.ident).map (EraseTermTypes.eraseTerm n) = names.map Expr.ident := by
  induction names with
  | nil => rfl
  | cons name rest ih => simp only [List.map_cons, EraseTermTypes.eraseTerm, mapCalls_ident, ih]

include fixed in
theorem eraseTerm_printTupleArgs (n : Nat) (request : Term) :
    (printTupleArgs n request).map (EraseTermTypes.eraseTerm n) = printTupleArgs n request := by
  unfold printTupleArgs
  cases hp : pairArgs? request with
  | some pair =>
    rcases pair with ⟨left, right⟩
    simp only [List.map_cons, List.map_nil, fixed]
  | none =>
    have hf := fixed n (.app "fst" (.cons request .nil))
    have hs := fixed n (.app "snd" (.cons request .nil))
    simp only [printTerm, printTerms] at hf hs
    simp only [List.map_cons, List.map_nil, hf, hs]

include fixed in
theorem eraseTerm_printMethodArgs (n : Nat) (row : Effect4.Program.Row) (request : Term) :
    (printMethodArgs n row request).map (EraseTermTypes.eraseTerm n) = printMethodArgs n row request := by
  unfold printMethodArgs
  split
  · rw [List.map_append, eraseTerm_printTupleArgs fixed, eraseTerm_trailing]
  · split
    · exact eraseTerm_trailing n row.trailing
    · simp only [List.map_cons, fixed, eraseTerm_trailing]

include fixed in
theorem eraseRowChildren_printMethod (n : Nat) (row : Effect4.Program.Row) (receiver request : Term)
    {x : Expr} (printed : printMethod n row receiver request = .ok x) :
    eraseRowChildren n x = x := by
  unfold printMethod at printed
  cases ht : rowTypeArgs row with
  | none => rw [ht] at printed; cases printed
  | some types =>
    rw [ht] at printed
    cases types with
    | nil =>
      cases printed
      simp only [eraseRowChildren, fixed, eraseTerm_printMethodArgs fixed]
    | cons first rest =>
      cases printed
      simp only [eraseRowChildren, EraseTermTypes.eraseTerm, mapCalls_generic]
      change Expr.call (.generic (.member (EraseTermTypes.eraseTerm n (printTerm n receiver))
        row.spelling) (first :: rest))
        ((printMethodArgs n row request).map (EraseTermTypes.eraseTerm n)) = _
      rw [fixed, eraseTerm_printMethodArgs fixed]

theorem eraseTerm_printRowHead (n : Nat) (row : Effect4.Program.Row) {head : Expr}
    (printed : printRowHead row = .ok head) : EraseTermTypes.eraseTerm n head = head := by
  unfold printRowHead at printed
  cases ht : rowTypeArgs row with
  | none => rw [ht] at printed; cases printed
  | some types =>
    rw [ht] at printed
    cases types with
    | nil => cases printed; rfl
    | cons first rest => cases printed; rfl

include fixed in
theorem eraseRowChildren_printRow (n : Nat) (row : Effect4.Program.Row) (request : Term)
    {x : Expr} (printed : printRow n row request = .ok x) : eraseRowChildren n x = x := by
  unfold printRow at printed
  cases shape : row.shape with
  | value => rw [shape] at printed; cases printed; rfl
  | call =>
    rw [shape] at printed
    cases hh : printRowHead row with
    | error reason => rw [hh] at printed; cases printed
    | ok head =>
      rw [hh] at printed
      simp only [bind, Except.bind] at printed
      split at printed
      · cases printed
        simp only [eraseRowChildren, eraseTerm_printRowHead n row hh, eraseTerm_trailing]
      · cases printed
        simp only [eraseRowChildren, eraseTerm_printRowHead n row hh, List.map_cons,
          fixed, eraseTerm_trailing]
  | tupleCall =>
    rw [shape] at printed
    cases hh : printRowHead row with
    | error reason => rw [hh] at printed; cases printed
    | ok head =>
      rw [hh] at printed
      simp only [bind, Except.bind] at printed
      cases printed
      simp only [eraseRowChildren, eraseTerm_printRowHead n row hh, List.map_append,
        eraseTerm_printTupleArgs fixed, eraseTerm_trailing]
  | method =>
    rw [shape] at printed
    cases hp : pairArgs? request with
    | none =>
      rw [hp] at printed
      exact eraseRowChildren_printMethod fixed n row _ _ printed
    | some pair =>
      rcases pair with ⟨receiver, args⟩
      rw [hp] at printed
      exact eraseRowChildren_printMethod fixed n row receiver args printed

end Effect4.Codegen

namespace Effect4.Codegen

open TypeScript Effect4.Program

theorem eraseRowChildren_withHeadTypes (n : Nat) (spelling : String) (types : List TypeRef)
    (plain typed : Expr) (fixed : eraseRowChildren n plain = plain)
    (inserted : withHeadTypes spelling types plain = .ok typed) :
    eraseRowChildren n typed = typed := by
  fun_cases withHeadTypes spelling types plain
  · cases inserted
    simp only [eraseRowChildren, EraseTermTypes.eraseTerm, mapCalls_ident] at fixed
    have argsFixed := (Expr.call.inj fixed).2
    simp only [eraseRowChildren, EraseTermTypes.eraseTerm, mapCalls_generic, mapCalls_ident]
    rw [argsFixed]
  · cases inserted
    simp only [eraseRowChildren] at fixed
    obtain ⟨receiverFixed, _, argsFixed⟩ := Expr.method.inj fixed
    change Expr.call (.generic (.member (EraseTermTypes.eraseTerm n _) _) types)
      (List.map (EraseTermTypes.eraseTerm n) _) = _
    rw [receiverFixed, argsFixed]
  · aesop (add norm simp withHeadTypes)

theorem eraseRowChildren_withFunction (n : Nat) (spelling : String) (plain fn typed : Expr)
    (fixed : eraseRowChildren n plain = plain) (functionFixed : EraseTermTypes.eraseTerm n fn = fn)
    (appended : withFunction spelling fn plain = .ok typed) : eraseRowChildren n typed = typed := by
  fun_cases withFunction spelling fn plain
  · cases appended
    simp only [eraseRowChildren] at fixed
    obtain ⟨headFixed, argsFixed⟩ := Expr.call.inj fixed
    simp only [eraseRowChildren, List.map_append, List.map_cons, List.map_nil,
      functionFixed, headFixed, argsFixed]
  · cases appended
    simp only [eraseRowChildren] at fixed
    obtain ⟨receiverFixed, _, argsFixed⟩ := Expr.method.inj fixed
    simp only [eraseRowChildren, List.map_append, List.map_cons, List.map_nil,
      functionFixed, receiverFixed, argsFixed]
  · aesop (add norm simp withFunction)

end Effect4.Codegen

namespace Effect4.Codegen

open TypeScript Effect4.Program

variable {Op : Type}

/-- An ordinary operation call retains its request, receiver and carried type arguments.
This is the row-child step of typed-print erasure (exact-codecs, R8). -/
theorem eraseRowChildren_printCall (sig : Signature Op) (n : Nat) (op : Op) (request : Term)
    {x : Expr} (printed : printCall sig n op request = .ok x) : eraseRowChildren n x = x := by
  unfold printCall at printed
  split at printed
  · exact eraseRowChildren_printRow EraseTermTypes.eraseTerm_printTerm_identity n _ request printed
  · split at printed
    · obtain ⟨plain, hp, ht⟩ := bind_eq_ok.mp printed
      exact eraseRowChildren_withHeadTypes n _ _ plain x
        (eraseRowChildren_printRow EraseTermTypes.eraseTerm_printTerm_identity n _ request hp) ht
    · cases printed

/-- The ordinary binder function preserves the environment increment used by its printed term.
This serves the complete row-call erasure law (exact-codecs, R8). -/
theorem eraseTerm_binder (n : Nat) (term : Term) :
    EraseTermTypes.eraseTerm n (Binders.write n [0] (printTerm (n + 1) term)) =
      Binders.write n [0] (printTerm (n + 1) term) := by
  simp only [Binders.write, Template.params, List.map_cons, List.map_nil,
    EraseTermTypes.eraseTerm_lambda, List.length_cons, List.length_nil,
    Nat.zero_add, EraseTermTypes.eraseTerm_printTerm_identity]

/-- The ordinary complete call retains its request and binder children under contextual erasure.
This serves the row-call connector of typed-print erasure (exact-codecs, R8). -/
theorem eraseRowChildren_printPerform (sig : Signature Op) (n : Nat) (op : Op) (request : Term)
    {x : Expr} (printed : printPerform sig n op request = .ok x) : eraseRowChildren n x = x := by
  unfold printPerform at printed
  split at printed
  · exact eraseRowChildren_printCall sig n op request printed
  · obtain ⟨plain, hp, ht⟩ := bind_eq_ok.mp printed
    exact eraseRowChildren_withFunction n _ plain _ x
      (eraseRowChildren_printCall sig n op request hp) (eraseTerm_binder n _) ht

/-- A raw annotated complete call also keeps its ordinary request and binder children.
Only the separate row-root inverse removes the inserted type arguments (exact-codecs, R8). -/
theorem eraseRowChildren_printPerformAt (sig : Signature Op) (n : Nat) (op : Op) (request : Term)
    (annotation : Option (List Ty)) {x : Expr}
    (printed : Templates.printPerformAt sig n op request annotation = .ok x) :
    eraseRowChildren n x = x := by
  cases annotation with
  | none => exact eraseRowChildren_printPerform sig n op request printed
  | some types =>
    cases types with
    | nil => exact eraseRowChildren_printPerform sig n op request printed
    | cons ty tys =>
      obtain ⟨plain, target, targets, hp, ht⟩ := printPerformAt_head printed
      exact eraseRowChildren_withHeadTypes n _ _ plain x
        (eraseRowChildren_printPerform sig n op request hp) ht

end Effect4.Codegen



 namespace Effect4.Codegen.Template

open TypeScript

theorem instAnn_congr (σ τ : Subst) : ∀ (ann : Option Nat),
    (∀ i ∈ holesAnn ann, lookup σ i = lookup τ i) → instAnn σ ann = instAnn τ ann
  | none, _ => rfl
  | some i, agree => by
    have hi := agree i (List.mem_singleton_self i)
    simp only [instAnn, hi]

mutual
  theorem inst_congr (n : Nat) (σ τ : Subst) : ∀ (t : Tpl),
      (∀ i ∈ holes t, lookup σ i = lookup τ i) → inst n σ t = inst n τ t
    | .hole i, agree => by
      have hi := agree i (List.mem_singleton_self i)
      simp only [inst, hi]
    | .strHole i, agree => by
      have hi := agree i (List.mem_singleton_self i)
      simp only [inst, hi]
    | .intHole i, agree => by
      have hi := agree i (List.mem_singleton_self i)
      simp only [inst, hi]
    | .arrHole i, agree => by
      have hi := agree i (List.mem_singleton_self i)
      simp only [inst, hi]
    | .binderRef _, _ => rfl
    | .ident _, _ => rfl
    | .str _, _ => rfl
    | .int _, _ => rfl
    | .bool _, _ => rfl
    | .call head args, agree => by
      have hh := inst_congr n σ τ head (fun i hi => agree i (List.mem_append_left _ hi))
      have ha := insts_congr n σ τ args (fun i hi => agree i (List.mem_append_right _ hi))
      simp only [inst, hh, ha]
    | .callSpread head i, agree => by
      have hh := inst_congr n σ τ head (fun j hj => agree j (List.mem_append_left _ hj))
      have hi := agree i (List.mem_append_right _ (List.mem_singleton_self i))
      simp only [inst, hh, hi]
    | .arr items, agree => by
      have hi := insts_congr n σ τ items agree
      simp only [inst, hi]
    | .object fields, agree => by
      have hf := instFields_congr n σ τ fields agree
      simp only [inst, hf]
    | .arrow body, agree => by
      have hb := inst_congr n σ τ body agree
      simp only [inst, hb]
    | .lambda binders body, agree => by
      have hb := inst_congr n σ τ body agree
      simp only [inst, hb]
    | .cond test yes no, agree => by
      have ht := inst_congr n σ τ test (fun i hi => agree i (List.mem_append_left _ hi))
      have hy := inst_congr n σ τ yes (fun i hi =>
        agree i (List.mem_append_right _ (List.mem_append_left _ hi)))
      have hn := inst_congr n σ τ no (fun i hi =>
        agree i (List.mem_append_right _ (List.mem_append_right _ hi)))
      simp only [inst, ht, hy, hn]
    | .method target name args, agree => by
      have ht := inst_congr n σ τ target (fun i hi => agree i (List.mem_append_left _ hi))
      have ha := insts_congr n σ τ args (fun i hi => agree i (List.mem_append_right _ hi))
      simp only [inst, ht, ha]
    | .arrowBlock binders body, agree => by
      have hb := instStmts_congr n σ τ body agree
      simp only [inst, hb]
    | .generator body, agree => by
      have hb := instStmts_congr n σ τ body agree
      simp only [inst, hb]
  theorem insts_congr (n : Nat) (σ τ : Subst) : ∀ (ts : Tpls),
      (∀ i ∈ holesTs ts, lookup σ i = lookup τ i) → insts n σ ts = insts n τ ts
    | .nil, _ => rfl
    | .cons head tail, agree => by
      have hh := inst_congr n σ τ head (fun i hi => agree i (List.mem_append_left _ hi))
      have ht := insts_congr n σ τ tail (fun i hi => agree i (List.mem_append_right _ hi))
      simp only [insts, hh, ht]
  theorem instFields_congr (n : Nat) (σ τ : Subst) : ∀ (fs : Fields),
      (∀ i ∈ holesFields fs, lookup σ i = lookup τ i) →
      instFields n σ fs = instFields n τ fs
    | .nil, _ => rfl
    | .cons key value tail, agree => by
      have hv := inst_congr n σ τ value (fun i hi => agree i (List.mem_append_left _ hi))
      have ht := instFields_congr n σ τ tail (fun i hi => agree i (List.mem_append_right _ hi))
      simp only [instFields, hv, ht]
  theorem instStmt_congr (n : Nat) (σ τ : Subst) : ∀ (t : StmtTpl),
      (∀ i ∈ holesStmt t, lookup σ i = lookup τ i) → instStmt n σ t = instStmt n τ t
    | .letInit k value ann, agree => by
      have hv := inst_congr n σ τ value (fun i hi => agree i (List.mem_append_left _ hi))
      have ha := instAnn_congr σ τ ann (fun i hi => agree i (List.mem_append_right _ hi))
      simp only [instStmt, hv, ha]
    | .assign k value, agree => by
      have hv := inst_congr n σ τ value agree
      simp only [instStmt, hv]
    | .ret value, agree => by
      have hv := inst_congr n σ τ value agree
      simp only [instStmt, hv]
    | .exprStmt value, agree => by
      have hv := inst_congr n σ τ value agree
      simp only [instStmt, hv]
    | .constYield k value, agree => by
      have hv := inst_congr n σ τ value agree
      simp only [instStmt, hv]
    | .yieldDiscard value, agree => by
      have hv := inst_congr n σ τ value agree
      simp only [instStmt, hv]
    | .ifElse test yes no, agree => by
      have ht := inst_congr n σ τ test (fun i hi => agree i (List.mem_append_left _ hi))
      have hy := instStmts_congr n σ τ yes (fun i hi =>
        agree i (List.mem_append_right _ (List.mem_append_left _ hi)))
      have hn := instStmts_congr n σ τ no (fun i hi =>
        agree i (List.mem_append_right _ (List.mem_append_right _ hi)))
      simp only [instStmt, ht, hy, hn]
    | .whileTrue body, agree => by
      have hb := instStmts_congr n σ τ body agree
      simp only [instStmt, hb]
    | .breakTo, _ => rfl
  theorem instStmts_congr (n : Nat) (σ τ : Subst) : ∀ (ts : StmtTpls),
      (∀ i ∈ holesStmts ts, lookup σ i = lookup τ i) → instStmts n σ ts = instStmts n τ ts
    | .nil, _ => rfl
    | .cons head tail, agree => by
      have hh := instStmt_congr n σ τ head (fun i hi => agree i (List.mem_append_left _ hi))
      have ht := instStmts_congr n σ τ tail (fun i hi => agree i (List.mem_append_right _ hi))
      simp only [instStmts, hh, ht]
    | .hole i, agree => by
      have hi := agree i (List.mem_singleton_self i)
      simp only [instStmts, hi]
end

end Effect4.Codegen.Template

namespace Effect4.Codegen.Template

/-- Mapping an attached substitution keeps its first matching key.
The callback retains the original capture membership needed by the size recursion. -/
theorem lookup_attach_map {σ : Subst} {i : Nat} {a : Arg}
    (read : lookup σ i = some a) (member : (i, a) ∈ σ)
    (f : { pair : Nat × Arg // pair ∈ σ } → Arg) :
    lookup (σ.attach.map fun entry => (entry.val.1, f entry)) i =
      some (f ⟨(i, a), member⟩) := by
  have found_map :
      (σ.attach.find? (fun entry => entry.val.1 == i)).map Subtype.val =
        σ.find? (fun pair => pair.1 == i) := by
    change (σ.attach.find? ((fun pair : Nat × Arg => pair.1 == i) ∘ Subtype.val)).map
      Subtype.val = _
    rw [← List.find?_map, List.attach_map_subtype_val]
  cases found : σ.attach.find? (fun entry => entry.val.1 == i) with
  | none =>
    rw [found] at found_map
    have absent : σ.find? (fun pair => pair.1 == i) = none := found_map.symm
    unfold lookup at read
    rw [absent] at read
    cases read
  | some entry =>
    have keyB : (entry.val.1 == i) = true :=
      List.find?_some (p := fun e : { pair : Nat × Arg // pair ∈ σ } => e.val.1 == i)
        (a := entry) found
    have key : entry.val.1 = i := eq_of_beq keyB
    have original : σ.find? (fun pair => pair.1 == i) = some entry.val := by
      rw [found] at found_map
      exact found_map.symm
    have value : entry.val.2 = a := by
      unfold lookup at read
      rw [original] at read
      exact Option.some.inj read
    have entry_eq : entry = ⟨(i, a), member⟩ := by
      apply Subtype.ext
      exact Prod.ext key value
    unfold lookup
    rw [List.find?_map]
    change ((σ.attach.find? (fun e => e.val.1 == i)).map
      (fun e => (e.val.1, f e))).map Prod.snd = _
    rw [found, entry_eq]
    rfl

end Effect4.Codegen.Template

namespace Effect4.Codegen

open TypeScript Effect4.Program Template

variable {Op : Type}

/-- The contextual capture map retains the first matching capture and its original membership.
This serves the typed-print erasure claim (exact-codecs, R8), at template reconstruction. -/
theorem eraseCaptures_lookup (row : Templates.Row) (sorts : List ArgSort) (n : Nat) (σ : Subst)
    (child : EffFam → Nat → (y : Expr) → (i : Nat) → (i, .expr y) ∈ σ → Expr)
    (children : EffFam → Nat → (ys : List Expr) → (i : Nat) → (i, .exprs ys) ∈ σ → List Expr)
    (block : Nat → (ss : List TypeScript.Stmt) → (i : Nat) → (i, .stmts ss) ∈ σ → List TypeScript.Stmt)
    {i : Nat} {a : Arg} (read : lookup σ i = some a) (member : (i, a) ∈ σ) :
    lookup (eraseCaptures row sorts n σ child children block) i =
      some (eraseCapture row sorts n σ child children block ⟨(i, a), member⟩) :=
  Template.lookup_attach_map read member (eraseCapture row sorts n σ child children block)

/-- A rigid template reconstructs the ordinary image from agreeing erased captures.
This serves the proposed typed-print erasure claim (exact-codecs, R8); capture agreement stays explicit. -/
theorem eraseExprRow_rigid_inst (classes : Classes.Classes) (sig : Signature Op)
    (spell : String → List String → Option Op) (fam : EffFam) (n : Nat) (x : Expr)
    (row : Templates.Row)
    (child : EffFam → Nat → (y : Expr) → sizeOf y < sizeOf x → Expr)
    (children : EffFam → Nat → (ys : List Expr) → sizeOf ys < sizeOf x → List Expr)
    (block : Nat → (ss : List TypeScript.Stmt) → sizeOf ss < sizeOf x → List TypeScript.Stmt)
    (same : (fam' : EffFam) → famRank fam' < famRank fam → Nat → Option Expr)
    (hfam : row.fam = fam) {t : Tpl} (hout : row.out = .tpl t)
    {sorts : List ArgSort} (hsorts : argSorts fam row.ctor = some sorts)
    {σ τ : Subst} (hσ : matchT n t x = some σ) (hrigid : t.rigid = true)
    {plain : Expr} (hplain : inst n τ t = some plain) :
    let μ := eraseCaptures row sorts n σ
      (fun fam' d y i hy => child fam' d y (match_below n t x σ hrigid hσ (i, .expr y) hy))
      (fun fam' d ys i hy => children fam' d ys (match_below n t x σ hrigid hσ (i, .exprs ys) hy))
      (fun d ss i hy => block d ss (match_below n t x σ hrigid hσ (i, .stmts ss) hy))
    (∀ i ∈ holes t, lookup μ i = lookup τ i) →
      eraseExprRow classes sig spell fam n x row child children block same = some plain := by
  dsimp only
  intro agree
  have hinst := Template.inst_congr n _ τ t agree
  unfold eraseExprRow
  simp only [hfam, hout, ↓reduceIte, hsorts, hrigid, ↓reduceDIte]
  split
  · rename_i absent
    rw [hσ] at absent
    cases absent
  · rename_i σ' matched
    have eq : σ' = σ := Option.some.inj (matched.symm.trans hσ)
    subst σ'
    rw [hinst, hplain]
    rfl

/-- A statement template reconstructs its ordinary image and declaration count from agreeing captures.
This serves the proposed typed-print erasure claim (exact-codecs, R8), at the statement spine. -/
theorem eraseStmtRow_inst (n : Nat) (s : TypeScript.Stmt) (row : Templates.Row)
    (child : EffFam → Nat → (y : Expr) → sizeOf y < sizeOf s → Expr)
    (children : EffFam → Nat → (ys : List Expr) → sizeOf ys < sizeOf s → List Expr)
    (block : Nat → (ss : List TypeScript.Stmt) → sizeOf ss < sizeOf s → List TypeScript.Stmt)
    (hfam : row.fam = .stmt) {t : StmtTpl} (hout : row.out = .stmt t)
    {sorts : List ArgSort} (hsorts : argSorts .stmt row.ctor = some sorts)
    {σ τ : Subst} (hσ : matchStmt n t s = some σ)
    {plain : TypeScript.Stmt} (hplain : instStmt n τ t = some plain) :
    let μ := eraseCaptures row sorts n σ
      (fun fam' d y i hy => child fam' d y (matchStmt_below n t s σ hσ (i, .expr y) hy))
      (fun fam' d ys i hy => children fam' d ys (matchStmt_below n t s σ hσ (i, .exprs ys) hy))
      (fun d ss i hy => block d ss (matchStmt_below n t s σ hσ (i, .stmts ss) hy))
    (∀ i ∈ holesStmt t, lookup μ i = lookup τ i) →
      eraseStmtRow n s row child children block = some (plain, t.declares) := by
  dsimp only
  intro agree
  have hinst := Template.instStmt_congr n _ τ t agree
  unfold eraseStmtRow
  simp only [hfam, hout, ↓reduceIte, hsorts]
  split
  · rename_i absent
    rw [hσ] at absent
    cases absent
  · rename_i σ' matched
    have eq : σ' = σ := Option.some.inj (matched.symm.trans hσ)
    subst σ'
    rw [hinst, hplain]
    rfl

end Effect4.Codegen

namespace Effect4.Codegen

open TypeScript Effect4.Program Template Templates

variable {Op : Type}

/-- Successful argument transport reconstructs the ordinary substitution and its captured holes.
This is the argument bridge of typed-print erasure (exact-codecs, R8), before template instantiation. -/
theorem eraseCaptures_printArgs (sig : Signature Op) (row : Templates.Row)
    (sorts : List ArgSort) (n : Nat) (σ : Subst)
    (child : EffFam → Nat → (y : Expr) → (i : Nat) → (i, .expr y) ∈ σ → Expr)
    (children : EffFam → Nat → (ys : List Expr) → (i : Nat) → (i, .exprs ys) ∈ σ → List Expr)
    (block : Nat → (ss : List TypeScript.Stmt) → (i : Nat) → (i, .stmts ss) ∈ σ → List TypeScript.Stmt)
    (typed plain : List (ArgF Op Carrier)) (lengths : typed.length = plain.length)
    (τ : Subst) (printed : printArgs sig row.fam n row.out typed 0 = .ok τ)
    (present : ∀ i ∈ row.out.holes, ∃ a, lookup τ i = some a)
    (matched : ∀ i ∈ row.out.holes, lookup σ i = lookup τ i)
    (transport : ∀ k ta pa, typed[k]? = some ta → plain[k]? = some pa → ∀ value,
      printArg sig (argDepth row.fam (argSortOf ta) n (row.out.levelAt k)) ta = .ok value →
      printArg sig (argDepth row.fam (argSortOf pa) n (row.out.levelAt k)) pa =
        .ok (value.map (eraseCaptureValue row sorts n σ child children block k))) :
    ∃ υ, printArgs sig row.fam n row.out plain 0 = .ok υ ∧
      ∀ i ∈ row.out.holes,
        lookup (eraseCaptures row sorts n σ child children block) i = lookup υ i := by
  obtain ⟨υ, printed', lookup'⟩ := printArgs_transport
    (eraseCaptureValue row sorts n σ child children block) typed plain 0 lengths
    (by simpa only [Nat.zero_add] using transport) τ printed
  refine ⟨υ, printed', ?_⟩
  intro i hi
  obtain ⟨a, found⟩ := present i hi
  have found' : lookup σ i = some a := (matched i hi).trans found
  obtain ⟨member, _⟩ := captured_of_lookup σ i a found'
  rw [eraseCaptures_lookup row sorts n σ child children block found' member,
    lookup' i, found, Option.map_some,
    eraseCaptureValue_at row sorts n σ child children block hi found' member]

end Effect4.Codegen


/-!
Helper obligations for typed-print erasure, exact-codecs and R8.
The row inverse must keep every call already accepted by the ordinary reader.
No typing or runtime property follows from this syntax property.
-/
namespace Effect4.Codegen
open TypeScript Effect4.Program Template Templates
variable {Op : Type} {classes : Classes.Classes} {sig : Signature Op}
  {spell : String → List String → Option Op}

theorem splitHeadTypes_bare_none {x bare : Expr} {targets : List TypeRef}
    (h : splitHeadTypes x = some (bare, targets)) : splitHeadTypes bare = none := by
  unfold splitHeadTypes at h
  split at h <;> cases h <;> rfl

theorem splitHeadTypes_targets_nonempty {x bare : Expr} {targets : List TypeRef}
    (h : splitHeadTypes x = some (bare, targets)) : targets ≠ [] := by
  unfold splitHeadTypes at h
  split at h <;> cases h <;> exact List.cons_ne_nil _ _

/-- Reading a bare call as an operation that carries no arguments excludes a typed head.
The row inverse consumes this refusal; the original reader remains unchanged. -/
theorem readCall_zero_excludes_head {n : Nat} {x bare : Expr} {targets : List TypeRef}
    {op : Op} {r : Term} (hsplit : splitHeadTypes x = some (bare, targets))
    (hbare : readCall classes sig spell n bare = .ok (.perform op r))
    (hnil : sig.typeArgsOf op = []) :
    ∃ why, readCall classes sig spell n x = .error why := by
  have hnone := splitHeadTypes_bare_none hsplit
  have hne := splitHeadTypes_targets_nonempty hsplit
  simp only [readCall, hnone] at hbare
  obtain ⟨face, hface, hfree⟩ := bind_eq_ok.mp hbare
  unfold typeFree at hfree
  split at hfree
  · rename_i op' r'
    split at hfree
    · cases hfree
      refine ⟨.arity (sig.rowOf op).spelling, ?_⟩
      simp only [readCall, hsplit, hface, installTypeArgs, hnil, List.length_nil]
      rw [if_neg]
      intro hlength
      exact hne (List.eq_nil_of_length_eq_zero hlength.symm)
    · exact nomatch hfree
  · exact nomatch hfree

/-- Successful term installation retains an operation's type-argument count.
The consumer checks the same head before and after installing a binder body. -/
theorem installTerm_keeps_types (hl : LawfulSpelling sig spell)
    {f : Term} {typed : Eff Op} {op : Op} {r : Term}
    (h : installTerm sig f typed = .ok (.perform op r)) :
    ∃ before, typed = .perform before r ∧ sig.typeArgsOf before = sig.typeArgsOf op := by
  unfold installTerm at h
  split at h
  · rename_i before request
    split at h
    · cases h
      exact ⟨before, rfl, (hl.typeArgs.typeArgsOf_withTerm before f).symm⟩
    · exact nomatch h
  · exact nomatch h

/-- A successful term-free check changes no operation or request. -/
theorem termFree_identity {typed : Eff Op} {op : Op} {r : Term}
    (h : termFree sig typed = .ok (.perform op r)) : typed = .perform op r := by
  unfold termFree at h
  split at h
  · split at h
    · cases h; rfl
    · exact nomatch h
  · exact nomatch h

/-- A pair of bare and annotated heads has the same final binder split.
A successful split retains the same annotation at the call before that binder. -/
theorem splitFunction_head_relation {n : Nat} {x bare : Expr} {targets : List TypeRef}
    (hsplit : splitHeadTypes x = some (bare, targets)) :
    (splitFunction n x = none ∧ splitFunction n bare = none) ∨
    ∃ call bareCall body,
      splitFunction n x = some (call, body) ∧
      splitFunction n bare = some (bareCall, body) ∧
      splitHeadTypes call = some (bareCall, targets) := by
  unfold splitHeadTypes at hsplit
  split at hsplit
  · rename_i name target rest args
    cases hsplit
    cases hlast : args.getLast? with
    | none =>
      left
      simp only [splitFunction, lastArgument?, hlast, Option.map_none, Option.bind_none, and_self]
    | some last =>
      cases hb : Binders.read n [0] last with
      | none =>
        left
        simp only [splitFunction, lastArgument?, hlast, Option.map_some, Option.bind_some,
          hb, Option.map_none, and_self]
      | some body =>
        right
        refine ⟨.call (.generic (.ident name) (target :: rest)) args.dropLast,
          .call (.ident name) args.dropLast, body, ?_, ?_, rfl⟩ <;>
          simp only [splitFunction, lastArgument?, hlast, Option.map_some, Option.bind_some, hb]
  · rename_i receiver name target rest args
    cases hsplit
    cases hlast : args.getLast? with
    | none =>
      left
      simp only [splitFunction, lastArgument?, hlast, Option.map_none, Option.bind_none, and_self]
    | some last =>
      cases hb : Binders.read n [0] last with
      | none =>
        left
        simp only [splitFunction, lastArgument?, hlast, Option.map_some, Option.bind_some,
          hb, Option.map_none, and_self]
      | some body =>
        right
        refine ⟨.call (.generic (.member receiver name) (target :: rest)) args.dropLast,
          .method receiver name args.dropLast, body, ?_, ?_, rfl⟩ <;>
          simp only [splitFunction, lastArgument?, hlast, Option.map_some, Option.bind_some, hb]
  · exact nomatch hsplit

/-- The ordinary reader never accepts an inserted generic head at a zero-arity operation.
The source is arbitrary syntax; no printed-image premise is needed. -/
theorem readPerform_zero_excludes_head (hl : LawfulSpelling sig spell)
    {n : Nat} {x bare : Expr} {targets : List TypeRef} {op : Op} {r : Term}
    (hsplit : splitHeadTypes x = some (bare, targets))
    (hbare : readPerform classes sig spell n bare = .ok (.perform op r))
    (hnil : sig.typeArgsOf op = []) {e : Eff Op}
    (hx : readPerform classes sig spell n x = .ok e) : False := by
  rcases splitFunction_head_relation (n := n) hsplit with ⟨hxnone, hbnone⟩ |
      ⟨call, bareCall, body, hxsome, hbsome, hcalls⟩
  · simp only [readPerform, hbnone] at hbare
    cases hbcall : readCall classes sig spell n bare with
    | error why => rw [hbcall] at hbare; exact nomatch hbare
    | ok typed =>
      rw [hbcall] at hbare
      have hid := termFree_identity hbare
      subst typed
      obtain ⟨why, hrefused⟩ := readCall_zero_excludes_head hsplit hbcall hnil
      simp only [readPerform, hxnone, hrefused] at hx
      exact nomatch hx
  · simp only [readPerform, hbsome] at hbare
    obtain ⟨typed, htyped, hbare⟩ := bind_eq_ok.mp hbare
    obtain ⟨f, hf, hbare⟩ := bind_eq_ok.mp hbare
    obtain ⟨before, heq, htypes⟩ := installTerm_keeps_types hl hbare
    subst typed
    obtain ⟨why, hrefused⟩ := readCall_zero_excludes_head hcalls htyped (htypes.trans hnil)
    simp only [readPerform, hxsome, hrefused] at hx
    exact nomatch hx

/-- Erasure preserves every call accepted by the ordinary reader.
This supplies the non-annotated row case of typed-print erasure. -/
theorem eraseRowJoin_readPerform (hl : LawfulSpelling sig spell)
    {n : Nat} {x : Expr} {e : Eff Op}
    (hread : readPerform classes sig spell n x = .ok e) :
    eraseRowJoin classes sig spell n x = x := by
  unfold eraseRowJoin
  split
  · rfl
  · rename_i bare targets hsplit
    split
    · rename_i op r hbare
      split
      · rename_i hempty
        simp only [Bool.and_eq_true] at hempty
        have hzero := List.nil_of_isEmpty hempty.1
        exact False.elim (readPerform_zero_excludes_head hl hsplit hbare hzero hread)
      · rfl
    · rfl

end Effect4.Codegen


/-!
Template selection for typed-print erasure, exact-codecs and R8.
The first successful row consumes the generic row reconstruction theorem.
Only successful syntax reconstruction is claimed, on the existing table.
-/
namespace Effect4.Codegen
open TypeScript Effect4.Program Template Templates

/-- Select the first successful row by its existing table index.
The erasure table has no diagnostic indices and uses this index-free projection. -/
theorem findSome?_of_index {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (k : Nat) (a : α) (v : β),
    (∀ j < k, ∀ b, l[j]? = some b → f b = none) →
    l[k]? = some a → f a = some v → l.findSome? f = some v
  | [], _, _, _, _, hk, _ => by cases hk
  | x :: xs, 0, a, v, _, hk, hv => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst a
    simp only [List.findSome?_cons, hv]
  | x :: xs, k + 1, a, v, hbefore, hk, hv => by
    have ih := findSome?_of_index f xs k a v
      (fun j hj b hb => hbefore (j + 1) (by omega) b (by
        simpa only [List.getElem?_cons_succ] using hb))
      (by simpa only [List.getElem?_cons_succ] using hk) hv
    have h0 := hbefore 0 (by omega) x rfl
    simp only [List.findSome?_cons, h0]
    exact ih

variable {Op : Type} {classes : Classes.Classes} {sig : Signature Op}
  {spell : String → List String → Option Op} {fam : EffFam} {n k : Nat}
  {input x plain : Expr}

/-- The normalized typed image selects the same existing table row.
The child callbacks are the production inverse, not assumed whole-program equations. -/
theorem eraseT_of_row {row : Templates.Row}
    (hnode : EraseTermTypes.eraseNode n input = x) (hk : Templates.table[k]? = some row)
    (hbefore : ∀ j < k, ∀ rj, Templates.table[j]? = some rj →
      eraseExprRow classes sig spell fam n x rj
        (fun fam' d y _ => (eraseT classes sig spell fam' d y).getD y)
        (fun fam' d ys _ => eraseSpine classes sig spell fam' d ys)
        (fun d body _ => eraseStmts classes sig spell d body)
        (fun fam' _ d => eraseT classes sig spell fam' d x) = none)
    (hat : eraseExprRow classes sig spell fam n x row
        (fun fam' d y _ => (eraseT classes sig spell fam' d y).getD y)
        (fun fam' d ys _ => eraseSpine classes sig spell fam' d ys)
        (fun d body _ => eraseStmts classes sig spell d body)
        (fun fam' _ d => eraseT classes sig spell fam' d x) = some plain) :
    eraseT classes sig spell fam n input = some plain := by
  rw [eraseT, hnode]
  exact findSome?_of_index _ Templates.table k row plain hbefore hk hat

end Effect4.Codegen



namespace Effect4.Codegen

open TypeScript Effect4.Program Template Templates

variable {Op : Type}

/-- The actual raw typed printer fills a child capture at its source address and binder depth.
This relation serves the argument bridge of typed-print erasure (exact-codecs, R8). -/
def TypedPrintsTo (sig : Signature Op) (ann : List Nat → Option (List Ty))
    (path : List Nat) (d : Nat) :
    (fam : EffFam) → EffSelfCarrier Op fam → Arg → Prop
  | .eff, v, .expr y => cata_eff (typedAlg sig ann) v path d = .ok y
  | .action, v, .expr y => cata_action (typedAlg sig ann) v path d = .ok y
  | .layer, v, .expr y => cata_layer (typedAlg sig ann) v path d = .ok y
  | .effs, v, .exprs ys => cata_effs (typedAlg sig ann) v path d = .ok ys
  | .layers, v, .exprs ys => cata_layers (typedAlg sig ann) v path d = .ok ys
  | .stmts, v, .stmts ss => cata_stmts (typedAlg sig ann) v path d = .ok ss
  | _, _, _ => False

/-- Successful typed child argument printing exposes the actual generated fold's result.
This is the inverse used by the source-address capture bridge (exact-codecs, R8). -/
theorem typedPrintsTo_of_printArg {sig : Signature Op} {ann : List Nat → Option (List Ty)}
    {path : List Nat} {d : Nat} {fam : EffFam} {c : EffSelfCarrier Op fam} {a : Arg}
    (printed : printArg sig d (.child fam (cataFam (typedAlg sig ann) fam c path)) =
      .ok (some a)) : TypedPrintsTo sig ann path d fam c a := by
  cases fam <;> cases a <;>
    aesop (add norm simp [TypedPrintsTo, cataFam, printArg, bind, Except.bind, pure, Except.pure])

end Effect4.Codegen



namespace Effect4.Codegen.Templates

open Effect4.Program

variable {Op : Type}

/-- Folding a source argument preserves whether it advances the child address.
This serves the source-position bridge of typed-print erasure (exact-codecs, R8). -/
theorem isChildArg_fold {R : EffFam → Type} (alg : EffAlgebra Op R)
    (source : ArgF Op (EffSelfCarrier Op)) : isChildArg (ArgF.fold alg source) = isChildArg source := by
  cases source <;> rfl

theorem countChildArgs_fold {R : EffFam → Type} (alg : EffAlgebra Op R)
    (args : List (ArgF Op (EffSelfCarrier Op))) (i : Nat) :
    (((args.map (ArgF.fold alg)).take i).countP isChildArg) = (args.take i).countP isChildArg := by
  rw [← List.map_take, List.countP_map]
  exact congrArg (fun f => (args.take i).countP f) (funext (isChildArg_fold alg))

/-- A typed source child prints at its actual position among the parent's recursive children.
The source scalar positions remain template indices (exact-codecs, R8). -/
theorem atAddress_fold_child (sig : Signature Op) (ann : List Nat → Option (List Ty))
    (path : List Nat) (args : List (ArgF Op (EffSelfCarrier Op))) (i : Nat)
    (fam : EffFam) (source : EffSelfCarrier Op fam)
    (member : args[i]? = some (.child fam source)) :
    (atAddress path (args.map (ArgF.fold (typedAlg sig ann))) 0)[i]? =
      some (.child fam (cataFam (typedAlg sig ann) fam source
        (path ++ [(args.take i).countP isChildArg]))) := by
  have folded : (args.map (ArgF.fold (typedAlg sig ann)))[i]? =
      some (.child fam (cataFam (typedAlg sig ann) fam source)) := by
    simp only [List.getElem?_map, member, Option.map_some, ArgF.fold]
  rw [atAddress_getElem_child path _ 0 i fam _ folded, countChildArgs_fold, Nat.zero_add]

/-- Addressing a scalar leaves the existing ordinary printer's source argument unchanged.
This is the scalar source-position step of typed-print erasure (exact-codecs, R8). -/
theorem atAddress_fold_leaf (sig : Signature Op) (ann : List Nat → Option (List Ty))
    (path : List Nat) (args : List (ArgF Op (EffSelfCarrier Op))) (i : Nat)
    (source : ArgF Op (EffSelfCarrier Op))
    (leaf : ∀ fam value, source ≠ .child fam value)
    (member : args[i]? = some source) :
    (atAddress path (args.map (ArgF.fold (typedAlg sig ann))) 0)[i]? =
      some (ArgF.fold (printAlg sig) source) := by
  rw [atAddress_getElem, List.getElem?_map, member, Option.map_some, Option.bind_some]
  cases source with
  | child fam value => exact False.elim (leaf fam value rfl)
  | term value => rfl
  | cause value => rfl
  | op value => rfl
  | nat value => rfl
  | mode value => rfl
  | bool value => rfl
  | key value => rfl
  | decision value => rfl
  | optTy value => rfl
  | forkOptions value => rfl
  | optTerm value => rfl
  | lit value => rfl
  | path value => rfl

end Effect4.Codegen.Templates



namespace Effect4.Codegen

open TypeScript Effect4.Program Template Templates

variable {Op : Type}

/-- The matched-hole adapter fixes each actually printed ordinary source scalar.
This is the scalar argument-transport step of typed-print erasure (exact-codecs, R8). -/
theorem eraseCaptureValue_printLeaf (sig : Signature Op) (row : Templates.Row)
    (sorts : List ArgSort) (n : Nat) (σ : Subst)
    (child : EffFam → Nat → (y : Expr) → (i : Nat) → (i, .expr y) ∈ σ → Expr)
    (children : EffFam → Nat → (ys : List Expr) → (i : Nat) → (i, .exprs ys) ∈ σ → List Expr)
    (block : Nat → (ss : List TypeScript.Stmt) → (i : Nat) → (i, .stmts ss) ∈ σ → List TypeScript.Stmt)
    (i : Nat) (source : ArgF Op (EffSelfCarrier Op))
    (leaf : ∀ fam value, source ≠ .child fam value)
    (sort : sorts[i]? = some (argSortOf source))
    (value : Option Arg)
    (printed : printArg sig (argDepth row.fam (argSortOf source) n (row.out.levelAt i))
      (ArgF.fold (printAlg sig) source) = .ok value)
    (matched : ∀ a, value = some a → i ∈ row.out.holes → lookup σ i = some a) :
    value.map (eraseCaptureValue row sorts n σ child children block i) = value := by
  cases value with
  | none => rfl
  | some capture =>
    simp only [Option.map_some]
    by_cases hole : i ∈ row.out.holes
    · have found := matched capture rfl hole
      have member := mem_of_lookup found
      rw [eraseCaptureValue_at row sorts n σ child children block hole found member,
        eraseCapture_printLeaf sig row sorts n σ child children block i source leaf sort
          capture member printed]
    · simp only [eraseCaptureValue, List.contains_eq_mem, hole, decide_false,
        Bool.false_eq_true, ↓reduceIte]

end Effect4.Codegen


/-!
# Typed row shape support

Placement: exact-codecs, R8; helper of the typed-print erasure claim.
Consumer: the structural typed-printer lift's rowCall branch.
Reach: successful Templates.printPerformAt, at any annotation and any eraser depth.
The existing LawfulSpelling premise separates row spellings from reserved program heads.
This helper adds no term-helper hygiene premise and proves no target execution.
The helpers serve row-call separation before inserted arguments erase.
-/


namespace Effect4.Codegen.TypedRowShapeSupport

open TypeScript Effect4.Program Template Templates

variable {Op : Type} {classes : Classes.Classes} {sig : Signature Op}
  {spell : String → List String → Option Op}

/-- The row owns every top-level identifier call head, bare or generic.
The generic clause records the actual spelling hidden from exprHead?. -/
def rowHeadOwned (spelling : String) (x : Expr) : Prop :=
  (∀ name args, x = .call (.ident name) args → name = spelling) ∧
  (∀ name types args, x = .call (.generic (.ident name) types) args → name = spelling)

/-- The ordinary row printer supplies head ownership, including declared arguments. -/
theorem printRow_rowHeadOwned {n : Nat} {row : Effect4.Program.Row} {r : Term} {x : Expr}
    (hp : printRow n row r = .ok x) : rowHeadOwned row.spelling x := by
  unfold printRow at hp
  aesop (add norm simp [printRowHead, printMethod, rowHeadOwned])

/-- Appending a binder function preserves the complete call's owned head. -/
theorem withFunction_rowHeadOwned {spelling : String} {call fn x : Expr}
    (hs : rowHeadOwned spelling call)
    (hp : withFunction spelling fn call = .ok x) : rowHeadOwned spelling x := by
  unfold withFunction at hp
  aesop (add norm simp [rowHeadOwned])

/-- Insertion keeps the bare call's actual spelling; methods remain generic members. -/
theorem withHeadTypes_rowHeadOwned {spelling : String} {call x : Expr} {types : List TypeRef}
    (hs : rowHeadOwned spelling call)
    (hp : withHeadTypes spelling types call = .ok x) : rowHeadOwned spelling x := by
  unfold withHeadTypes at hp
  aesop (add norm simp [rowHeadOwned])

/-- Operation-owned arguments preserve the row's head ownership. -/
theorem printCall_rowHeadOwned {n : Nat} {op : Op} {r : Term} {x : Expr}
    (hp : printCall sig n op r = .ok x) : rowHeadOwned (sig.rowOf op).spelling x := by
  unfold printCall at hp
  split at hp
  · exact printRow_rowHeadOwned hp
  · split at hp
    · obtain ⟨plain, hplain, hhead⟩ := bind_eq_ok.mp hp
      exact withHeadTypes_rowHeadOwned (printRow_rowHeadOwned hplain) hhead
    · exact nomatch hp

/-- The complete ordinary operation call retains its head when its binder is appended. -/
theorem printPerform_rowHeadOwned {n : Nat} {op : Op} {r : Term} {x : Expr}
    (hp : printPerform sig n op r = .ok x) : rowHeadOwned (sig.rowOf op).spelling x := by
  unfold printPerform at hp
  split at hp
  · exact printCall_rowHeadOwned hp
  · obtain ⟨call, hcall, hfunction⟩ := bind_eq_ok.mp hp
    exact withFunction_rowHeadOwned (printCall_rowHeadOwned hcall) hfunction

/-- The actual generic head remains the row spelling under a nonempty annotation. -/
theorem printPerformAt_rowHeadOwned {n : Nat} {op : Op} {r : Term}
    {annotation : Option (List Ty)} {x : Expr}
    (hp : Templates.printPerformAt sig n op r annotation = .ok x) :
    rowHeadOwned (sig.rowOf op).spelling x := by
  cases annotation with
  | none => exact printPerform_rowHeadOwned hp
  | some types =>
    cases types with
    | nil => exact printPerform_rowHeadOwned hp
    | cons ty tys =>
      obtain ⟨plain, target, targets, hplain, hhead⟩ := printPerformAt_head hp
      exact withHeadTypes_rowHeadOwned (printPerform_rowHeadOwned hplain) hhead

/-- A typed row call remains a program node, at every successful annotation. -/
theorem printPerformAt_nodeLike {n : Nat} {op : Op} {r : Term}
    {annotation : Option (List Ty)} {x : Expr}
    (hp : Templates.printPerformAt sig n op r annotation = .ok x) : nodeLike x = true := by
  cases annotation with
  | none => exact printPerform_nodeLike hp
  | some types =>
    cases types with
    | nil => exact printPerform_nodeLike hp
    | cons ty tys =>
      obtain ⟨plain, target, targets, hplain, hhead⟩ := printPerformAt_head hp
      exact (withHeadTypes_head hhead).2

/-- Reserved skeletons cannot claim an annotated row call at any matching depth. -/
theorem printPerformAt_no_reserved (hl : LawfulSpelling sig spell) {n : Nat} {op : Op}
    {r : Term} {annotation : Option (List Ty)} {x : Expr}
    (hp : Templates.printPerformAt sig n op r annotation = .ok x)
    (d : Nat) (t : Tpl) (h : String) (hh : t.head? = some h) (hres : h ∈ reserved) :
    matchT d t x = none := by
  cases annotation with
  | none => exact matchT_none_of_reserved hl hp hh hres
  | some types =>
    cases types with
    | nil => exact matchT_none_of_reserved hl hp hh hres
    | cons ty tys =>
      obtain ⟨plain, target, targets, hplain, hhead⟩ := printPerformAt_head hp
      have hnone := (withHeadTypes_head hhead).1
      cases hm : matchT d t x with
      | none => rfl
      | some substitution =>
        have hactual := head_of_match d t x substitution hm hh
        rw [hactual] at hnone
        exact nomatch hnone

/-- The node inverse cannot erase a nonreserved generic identifier call.
Unlike exprHead?, this premise observes the actual generic head spelling. -/
theorem eraseNode_of_genericHead_not_reserved {x : Expr}
    (hnot : ∀ name types args, x = .call (.generic (.ident name) types) args → name ∉ reserved)
    (d : Nat) : EraseTermTypes.eraseNode d x = x := by
  fun_cases EraseTermTypes.eraseNode d x <;>
    aesop (add norm simp [List.contains_eq_mem, reserved, heads, Head.spelling])

/-- A successful typed row keeps every node-level argument at every eraser depth.
This follows from actual row spelling ownership and the existing reserved-head separation. -/
theorem eraseNode_printPerformAt (hl : LawfulSpelling sig spell) {n : Nat} {op : Op}
    {r : Term} {annotation : Option (List Ty)} {x : Expr}
    (hp : Templates.printPerformAt sig n op r annotation = .ok x) (d : Nat) :
    EraseTermTypes.eraseNode d x = x := by
  have hs := printPerformAt_rowHeadOwned hp
  apply eraseNode_of_genericHead_not_reserved
  intro name types args heq
  rw [hs.2 name types args heq]
  exact hl.spelling_not_reserved op

/-- The action-family eraser refuses a row image without inspecting its children.
The structural lift uses this at the transparent eff-to-action row. -/
theorem eraseT_action_none_of_printPerformAt (hl : LawfulSpelling sig spell) {n : Nat} {op : Op}
    {r : Term} {annotation : Option (List Ty)} {x : Expr}
    (hp : Templates.printPerformAt sig n op r annotation = .ok x) (d : Nat) :
    eraseT classes sig spell .action d x = none := by
  rw [eraseT, eraseNode_printPerformAt hl hp d, List.findSome?_eq_none_iff]
  intro row hmem
  have hshape := table_fact table_actionHeaded hmem
  simp only [actionRowHeaded, bne_iff_ne, ne_eq, Bool.or_eq_true] at hshape
  rcases hshape with hfam | hshape
  · exact eraseExprRow_none_of_fam hfam
  · split at hshape
    · rename_i t hout
      simp only [Bool.and_eq_true, Option.any_eq_true] at hshape
      obtain ⟨_, h, hh, hres⟩ := hshape
      exact eraseExprRow_none_of_nomatch hout
        (printPerformAt_no_reserved hl hp d t h hh (List.mem_of_elem_eq_true hres))
    · rename_i name hout
      exact eraseExprRow_none_of_refuse hout
    · cases hshape

end Effect4.Codegen.TypedRowShapeSupport



namespace Effect4.Codegen

open TypeScript Effect4.Program Template Templates

variable {Op : Type}

set_option maxHeartbeats 2000000 in

/-- Source positions supply the actual scalar and recursive-child laws for argument transport.
This serves typed-print erasure (exact-codecs, R8), at the generic template row.
The hole premise comes from the existing table's completeness law. -/
theorem source_printArgs_transport (classes : Classes.Classes) (sig : Signature Op)
    (ann : List Nat → Option (List Ty)) (path : List Nat)
    (row : Templates.Row) (n : Nat) (args : List (ArgF Op (EffSelfCarrier Op)))
    (σ : Subst)
    (child : EffFam → Nat → (y : Expr) → (i : Nat) → (i, .expr y) ∈ σ → Expr)
    (children : EffFam → Nat → (ys : List Expr) → (i : Nat) → (i, .exprs ys) ∈ σ → List Expr)
    (block : Nat → (ss : List TypeScript.Stmt) → (i : Nat) → (i, .stmts ss) ∈ σ → List TypeScript.Stmt)
    (τ : Subst)
    (printed : printArgs sig row.fam n row.out
      (atAddress path (args.map (ArgF.fold (typedAlg sig ann))) 0) 0 = .ok τ)
    (matched : ∀ i ∈ row.out.holes, lookup σ i = lookup τ i)
    (readable : argsReadable classes sig row.fam n row.out (rowDaemon row)
      (args.map (ArgF.fold (readableAlg classes sig))) 0 = true)
    (holes : ∀ i fam source, args[i]? = some (.child fam source) → i ∈ row.out.holes)
    (recursive : ∀ i fam source, args[i]? = some (.child fam source) →
      ∀ capture (member : (i, capture) ∈ σ),
      let depth := argDepth row.fam (.child fam) n (row.out.levelAt i)
      ReadableAt classes sig fam source depth →
      TypedPrintsTo sig ann (path ++ [(args.take i).countP isChildArg]) depth fam source capture →
      PrintsTo sig depth fam source
        (eraseCapture row (args.map argSortOf) n σ child children block ⟨(i, capture), member⟩)) :
    ∀ k ta pa,
      (atAddress path (args.map (ArgF.fold (typedAlg sig ann))) 0)[k]? = some ta →
      (args.map (ArgF.fold (printAlg sig)))[k]? = some pa → ∀ value,
      printArg sig (argDepth row.fam (argSortOf ta) n (row.out.levelAt k)) ta = .ok value →
      printArg sig (argDepth row.fam (argSortOf pa) n (row.out.levelAt k)) pa =
        .ok (value.map (eraseCaptureValue row (args.map argSortOf) n σ child children block k)) := by
  intro k ta pa ht hp value hv
  rw [List.getElem?_map] at hp
  obtain ⟨source, hsource, rfl⟩ := Option.map_eq_some_iff.mp hp
  have value_at := (printArgs_lookup _ 0 τ printed).1 k ta ht
  simp only [Nat.zero_add] at value_at
  have lookup_value : lookup τ k = value := Except.ok.inj (value_at.symm.trans hv)
  have source_sort : (args.map argSortOf)[k]? = some (argSortOf source) := by
    simp only [List.getElem?_map, hsource, Option.map_some]
  have scalar : ∀ s : ArgF Op (EffSelfCarrier Op), args[k]? = some s →
      (∀ fam child, s ≠ .child fam child) →
      printArg sig (argDepth row.fam (argSortOf (ArgF.fold (printAlg sig) s)) n
        (row.out.levelAt k)) (ArgF.fold (printAlg sig) s) =
        .ok (value.map (eraseCaptureValue row (args.map argSortOf) n σ child children block k)) := by
    intro s hs leaf
    have typed_at := atAddress_fold_leaf sig ann path args k s leaf hs
    have typed_eq := Option.some.inj (ht.symm.trans typed_at)
    have hprint := hv
    rw [typed_eq, argSortOf_fold] at hprint
    have hsort : (args.map argSortOf)[k]? = some (argSortOf s) := by
      simp only [List.getElem?_map, hs, Option.map_some]
    rw [argSortOf_fold,
      eraseCaptureValue_printLeaf sig row (args.map argSortOf) n σ child children block
        k s leaf hsort value hprint (fun a eq hole =>
          (matched k hole).trans (lookup_value.trans eq))]
    exact hprint
  cases source with
  | child fam source =>
    have typed_at := atAddress_fold_child sig ann path args k fam source hsource
    have typed_eq := Option.some.inj (ht.symm.trans typed_at)
    subst ta
    simp only [ArgF.fold, argSortOf] at hv ⊢
    cases value with
    | none =>
      have stmt : fam = .stmt := by
        cases fam <;> aesop (add norm simp [printArg, bind, Except.bind, pure, Except.pure])
      subst fam
      rfl
    | some capture =>
      have hole := holes k fam source hsource
      have found : lookup σ k = some capture := (matched k hole).trans lookup_value
      have member := mem_of_lookup found
      have domain := argsReadable_at (args.map (ArgF.fold (readableAlg classes sig)))
        0 k (ArgF.fold (readableAlg classes sig) (.child fam source)) readable
        (by simp only [List.getElem?_map, hsource, Option.map_some])
      simp only [argSortOf, Nat.zero_add] at domain
      have plain := recursive k fam source hsource capture member
        (readableAt_of_argReadable domain) (typedPrintsTo_of_printArg hv)
      have plainPrinted := printArg_child sig _ fam source _ plain
      rw [Option.map_some, eraseCaptureValue_at row (args.map argSortOf) n σ
        child children block hole found member]
      exact plainPrinted
  | _ =>
    exact scalar _ hsource (fun fam child eq => by cases eq)

end Effect4.Codegen



namespace Effect4.Codegen

open TypeScript Effect4.Program Template Templates

variable {Op : Type}

/-- A classifier supplies scalar values, never a recursive source child.
This serves the source-capture bridge of typed-print erasure (exact-codecs, R8). -/
theorem supplied_ne_child (row : Templates.Row) (i : Nat) (fam : EffFam)
    (source : EffSelfCarrier Op fam) :
    row.supplied (Op := Op) (R := EffSelfCarrier Op) i ≠ some (.child fam source) := by
  intro h
  unfold Templates.Row.supplied at h
  obtain ⟨p, _, hp⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨j, pattern⟩ := p
  cases pattern with
  | is value => cases value <;> cases hp
  | _ => cases hp

theorem supplied_child_isSome_false {row : Templates.Row} {fam : EffFam} {ctor : String}
    {args : List (ArgF Op (EffSelfCarrier Op))} (selected : row.selects fam ctor args = true)
    (i : Nat) (childFam : EffFam) (source : EffSelfCarrier Op childFam)
    (member : args[i]? = some (.child childFam source)) :
    (row.supplied (Op := Op) (R := EffSelfCarrier Op) i).isSome = false := by
  cases supplied : row.supplied i with
  | none => rfl
  | some value =>
    have eq := supplied_eq_of_selects row selected i (.child childFam source) member value supplied
    subst value
    exact False.elim (supplied_ne_child row i childFam source supplied)

/-- The existing complete expression template captures every recursive source child.
This discharges the hole premise of source argument transport (exact-codecs, R8). -/
theorem source_child_hole {row : Templates.Row} (inTable : row ∈ Templates.table)
    {fam : EffFam} {ctor : String} {args : List (ArgF Op (EffSelfCarrier Op))}
    (selected : row.selects fam ctor args = true)
    (sorts : argSorts row.fam row.ctor = some (args.map argSortOf))
    {t : Tpl} (output : row.out = .tpl t)
    (i : Nat) (childFam : EffFam) (source : EffSelfCarrier Op childFam)
    (member : args[i]? = some (.child childFam source)) : i ∈ row.out.holes := by
  exact hole_of_not_supplied inTable output sorts i
    (by rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp member).1)
    (supplied_child_isSome_false selected i childFam source member)

/-- The existing complete statement template captures every recursive source child.
This discharges the statement argument transport premise (exact-codecs, R8). -/
theorem source_child_hole_stmt {row : Templates.Row} (inTable : row ∈ Templates.table)
    {fam : EffFam} {ctor : String} {args : List (ArgF Op (EffSelfCarrier Op))}
    (selected : row.selects fam ctor args = true)
    (sorts : argSorts row.fam row.ctor = some (args.map argSortOf))
    {t : StmtTpl} (output : row.out = .stmt t)
    (i : Nat) (childFam : EffFam) (source : EffSelfCarrier Op childFam)
    (member : args[i]? = some (.child childFam source)) : i ∈ row.out.holes := by
  exact hole_of_not_supplied_stmt inTable output sorts i
    (by rw [List.length_map]; exact (List.getElem?_eq_some_iff.mp member).1)
    (supplied_child_isSome_false selected i childFam source member)

end Effect4.Codegen



namespace Effect4.Codegen

open TypeScript Effect4.Program Template Templates

variable {Op : Type} {classes : Classes.Classes} {sig : Signature Op}
  {spell : String → List String → Option Op}

/-- Every successful raw row annotation erases to its ordinary complete call.
This serves the row branch of typed-print erasure (exact-codecs, R8), under the old readable premises. -/
theorem eraseRowJoin_printPerformAt_total (hl : LawfulSpelling sig spell) {n : Nat} {op : Op}
    {r : Term} (hd : sig.dom op = true)
    (hreq : requestReadable (sig.rowOf op) n r = true) (hc : r.covers classes = true)
    (hu : r.unannotated = true)
    (htypes : typeArgsReadable (sig.rowOf op) (sig.typeArgsOf op) = true)
    (hterm : termReadable classes n (sig.rowOf op) ((sig.termOf op).map (·.term)) = true)
    {annotation : Option (List Ty)} {typed : Expr}
    (printed : Templates.printPerformAt sig n op r annotation = .ok typed) :
    ∃ plain, printPerform sig n op r = .ok plain ∧
      eraseRowJoin classes sig spell n typed = plain := by
  cases annotation with
  | none =>
    exact ⟨typed, printed, eraseRowJoin_readPerform hl
      (readPerform_printPerform hl hd hreq hc hu htypes hterm printed)⟩
  | some types =>
    cases types with
    | nil =>
      exact ⟨typed, printed, eraseRowJoin_readPerform hl
        (readPerform_printPerform hl hd hreq hc hu htypes hterm printed)⟩
    | cons ty tys =>
      exact ⟨_, eraseRowJoin_printPerformAt hl hd hreq hc hu htypes hterm printed, rfl⟩

/-- The row template erases a raw typed operation with its actual complete-call reader.
The source/table lift supplies first-match separation; no callback agreement is assumed here. -/
theorem eraseExprRow_printPerformAt (hl : LawfulSpelling sig spell) {n : Nat} {op : Op}
    {r : Term} (hd : sig.dom op = true)
    (hreq : requestReadable (sig.rowOf op) n r = true) (hc : r.covers classes = true)
    (hu : r.unannotated = true)
    (htypes : typeArgsReadable (sig.rowOf op) (sig.typeArgsOf op) = true)
    (hterm : termReadable classes n (sig.rowOf op) ((sig.termOf op).map (·.term)) = true)
    {annotation : Option (List Ty)} {typed : Expr}
    (printed : Templates.printPerformAt sig n op r annotation = .ok typed)
    (row : Templates.Row) (family : row.fam = .eff) (output : row.out = .rowCall)
    (child : EffFam → Nat → (y : Expr) → sizeOf y < sizeOf typed → Expr)
    (children : EffFam → Nat → (ys : List Expr) → sizeOf ys < sizeOf typed → List Expr)
    (block : Nat → (ss : List TypeScript.Stmt) → sizeOf ss < sizeOf typed → List TypeScript.Stmt)
    (same : (fam' : EffFam) → famRank fam' < famRank .eff → Nat → Option Expr) :
    ∃ plain, printPerform sig n op r = .ok plain ∧
      eraseExprRow classes sig spell .eff n typed row child children block same = some plain := by
  obtain ⟨plain, ordinary, erased⟩ :=
    eraseRowJoin_printPerformAt_total hl hd hreq hc hu htypes hterm printed
  refine ⟨plain, ordinary, ?_⟩
  simp only [eraseExprRow, family, output, ↓reduceIte,
    eraseRowChildren_printPerformAt sig n op r _ printed, erased,
    readPerform_printPerform hl hd hreq hc hu htypes hterm ordinary]

end Effect4.Codegen


/-!
The expression-list step of typed-print erasure, exact-codecs and R8.
The existing printer's two child slots supply the addresses.
The source list is folded by the generated algebra, not a second program traversal.
This file expects the checked TypedPrintsTo definition in Laws.Codegen.PrintTyped.
-/
namespace Effect4.Codegen
open TypeScript Effect4.Program Template Templates
variable {Op : Type} {classes : Classes.Classes} {sig : Signature Op}
  {spell : String → List String → Option Op} {ann : List Nat → Option (List Ty)}

/-- The generated typed spine has two children, at indices zero and one.
The tail extends the source address; it does not reuse the head's address. -/
theorem typed_effs_cons (e : Eff Op) (es : Effs Op) (path : List Nat) (n : Nat) :
    cata_effs (typedAlg sig ann) (.cons e es) path n =
      (cata_eff (typedAlg sig ann) e (path ++ [0]) n).bind fun y =>
        (cata_effs (typedAlg sig ann) es (path ++ [1]) n).bind fun ys => .ok (y :: ys) := rfl

theorem typed_layers_cons (e : LayerTerm Op) (es : LayerTerms Op) (path : List Nat) (n : Nat) :
    cata_layers (typedAlg sig ann) (.cons e es) path n =
      (cata_layer (typedAlg sig ann) e (path ++ [0]) n).bind fun y =>
        (cata_layers (typedAlg sig ann) es (path ++ [1]) n).bind fun ys => .ok (y :: ys) := rfl

/-- Reconstruct a typed expression-list image from the smaller expression and list images.
Its consumer is the well-founded family erasure theorem. -/
theorem eraseSpine_print_step {m : Nat}
    (hexpr : ∀ fam path n (e : EffSelfCarrier Op fam) (y : Expr), sizeOf y < m →
      ReadableAt classes sig fam e n → TypedPrintsTo sig ann path n fam e (.expr y) →
      ∃ plain, eraseT classes sig spell fam n y = some plain ∧ PrintsTo sig n fam e (.expr plain))
    (hlist : ∀ fam path n (e : EffSelfCarrier Op fam) (ys : List Expr), sizeOf ys < m →
      ReadableAt classes sig fam e n → TypedPrintsTo sig ann path n fam e (.exprs ys) →
      PrintsTo sig n fam e (.exprs (eraseSpine classes sig spell fam n ys))) :
    ∀ fam path n (e : EffSelfCarrier Op fam) (xs : List Expr), sizeOf xs ≤ m →
      ReadableAt classes sig fam e n → TypedPrintsTo sig ann path n fam e (.exprs xs) →
      PrintsTo sig n fam e (.exprs (eraseSpine classes sig spell fam n xs))
  | .effs, path, n, e, xs, hx, hr, hp => by
    cases e with
    | nil =>
      simp only [TypedPrintsTo] at hp
      cases hp
      rw [eraseSpine]
      rfl
    | cons e es =>
      simp only [TypedPrintsTo, typed_effs_cons] at hp
      obtain ⟨y, hy, hp⟩ := bind_eq_ok.mp hp
      obtain ⟨rest, hrest, hxs⟩ := bind_eq_ok.mp hp
      cases hxs
      obtain ⟨d, hd⟩ := hr
      simp only [cataFam, dom_effs_cons, Option.bind_eq_some_iff] at hd
      obtain ⟨d1, hd1, d2, hd2, _⟩ := hd
      have hsz : sizeOf (y :: rest) = 1 + sizeOf y + sizeOf rest := List.cons.sizeOf_spec y rest
      obtain ⟨plain, herase, hplain⟩ := hexpr .eff (path ++ [0]) n e y (by omega) ⟨d1, hd1⟩ hy
      have htail := hlist .effs (path ++ [1]) n es rest (by omega) ⟨d2, hd2⟩ hrest
      simp only [PrintsTo] at hplain htail ⊢
      rw [eraseSpine]
      change cata_effs (printAlg sig) (.cons e es) n = .ok
        ((eraseT classes sig spell .eff n y).getD y :: eraseSpine classes sig spell .effs n rest)
      rw [herase]
      simp only [Option.getD_some, cata_effs_cons, hplain, htail, ok_bind]
      rfl
  | .layers, path, n, e, xs, hx, hr, hp => by
    cases e with
    | nil =>
      simp only [TypedPrintsTo] at hp
      cases hp
      rw [eraseSpine]
      rfl
    | cons e es =>
      simp only [TypedPrintsTo, typed_layers_cons] at hp
      obtain ⟨y, hy, hp⟩ := bind_eq_ok.mp hp
      obtain ⟨rest, hrest, hxs⟩ := bind_eq_ok.mp hp
      cases hxs
      obtain ⟨d, hd⟩ := hr
      simp only [cataFam, dom_layers_cons, Option.bind_eq_some_iff] at hd
      obtain ⟨d1, hd1, d2, hd2, _⟩ := hd
      have hsz : sizeOf (y :: rest) = 1 + sizeOf y + sizeOf rest := List.cons.sizeOf_spec y rest
      obtain ⟨plain, herase, hplain⟩ := hexpr .layer (path ++ [0]) n e y (by omega) ⟨d1, hd1⟩ hy
      have htail := hlist .layers (path ++ [1]) n es rest (by omega) ⟨d2, hd2⟩ hrest
      simp only [PrintsTo] at hplain htail ⊢
      rw [eraseSpine]
      change cata_layers (printAlg sig) (.cons e es) n = .ok
        ((eraseT classes sig spell .layer n y).getD y :: eraseSpine classes sig spell .layers n rest)
      rw [herase]
      simp only [Option.getD_some, cata_layers_cons, hplain, htail, ok_bind]
      rfl
  | .eff, _, _, _, _, _, _, hp => by simp only [TypedPrintsTo] at hp
  | .action, _, _, _, _, _, _, hp => by simp only [TypedPrintsTo] at hp
  | .layer, _, _, _, _, _, _, hp => by simp only [TypedPrintsTo] at hp
  | .stmt, _, _, _, _, _, _, hp => by simp only [TypedPrintsTo] at hp
  | .stmts, _, _, _, _, _, _, hp => by simp only [TypedPrintsTo] at hp

end Effect4.Codegen


/-!
Addressing preserves the template classifier and the number of source arguments.
These helpers serve the expression and statement steps of typed-print erasure,
under exact-codecs and R8. They change no syntax or admission judgment.
-/
set_option autoImplicit false

namespace Effect4.Codegen.Templates
open Effect4.Program
variable {Op : Type}

/-- A row classifier never tests a recursive child's carrier. -/
theorem ArgPat.holds_child {R : EffFam → Type} (p : ArgPat)
    (fam : EffFam) (child : R fam) : p.holds (.child fam child : ArgF Op R) = false := by
  cases p with
  | is value => cases value <;> rfl
  | _ => rfl

/-- Addressing a child does not alter the row's test of its source argument. -/
theorem patternAt_atAddress (path : List Nat) (args : List (ArgF Op TCarrier))
    (j i : Nat) (p : ArgPat) :
    patternAt (atAddress path args j) i p = patternAt args i p := by
  unfold patternAt
  rw [atAddress_getElem]
  cases args[i]? with
  | none => rfl
  | some a =>
    cases a with
    | child fam child =>
      simp only [Option.bind_some, atAddress, List.getElem?_cons_zero, ArgPat.holds_child]
    | _ =>
      simp only [Option.bind_some, atAddress, List.getElem?_cons_zero]
      aesop (add norm simp [ArgPat.holds, Fixed.holds])

/-- Both printers select the same row after child addressing. -/
theorem selects_atAddress (row : Row) (fam : EffFam) (ctor : String)
    (path : List Nat) (args : List (ArgF Op TCarrier)) (j : Nat) :
    row.selects fam ctor (atAddress path args j) = row.selects fam ctor args := by
  unfold Row.selects
  simp only [patternAt_atAddress]

/-- The address carrier preserves every argument, including scalar arguments. -/
theorem length_atAddress (path : List Nat) (args : List (ArgF Op TCarrier)) (j : Nat) :
    (atAddress path args j).length = args.length := by
  have h := congrArg List.length (argSortOf_atAddress path args j)
  simpa only [List.length_map] using h

end Effect4.Codegen.Templates


/-!
The selected statement row reconstructs its ordinary printed syntax after erasure.
This is a helper of typed-print erasure, exact-codecs and R8. Its consumer is
eraseStmts_print_step. The callbacks are the smaller-target induction hypotheses.
Readable syntax and the actual typed printer result remain explicit premises.
No TypeScript typing or runtime observation is asserted.
-/
set_option autoImplicit false
namespace Effect4.Codegen
open TypeScript Effect4.Program Template Templates
variable {Op : Type} {classes : Classes.Classes} {sig : Signature Op}
  {spell : String → List String → Option Op} {ann : List Nat → Option (List Ty)}

/-- A prior statement template cannot consume the later template's printed former. -/
theorem eraseStmtRow_earlier_none {n : Nat} {s : TypeScript.Stmt}
    (child : EffFam → Nat → (y : Expr) → sizeOf y < sizeOf s → Expr)
    (children : EffFam → Nat → (ys : List Expr) → sizeOf ys < sizeOf s → List Expr)
    (block : Nat → (ss : List TypeScript.Stmt) → sizeOf ss < sizeOf s → List TypeScript.Stmt)
    {rj row : Templates.Row} (apart : rowsApart rj row = true)
    {t : StmtTpl} (output : row.out = .stmt t) {τ : Subst}
    (printed : instStmt n τ t = some s) :
    eraseStmtRow n s rj child children block = none := by
  unfold rowsApart at apart
  rw [output] at apart
  simp only at apart
  split at apart
  · rename_i t' output'
    simp only [bne_iff_ne, ne_eq] at apart
    have hm := matchStmt_former n τ t' t s apart printed
    unfold eraseStmtRow
    simp only [output']
    split
    · split
      · rfl
      · rename_i σ hs
        rw [hm] at hs
        cases hs
    · rfl
  · rename_i other
    unfold eraseStmtRow
    split
    · cases h : rj.out with
      | stmt t' => exact False.elim (other t' h)
      | _ => rfl
    · rfl

set_option maxHeartbeats 2000000 in
/-- The statement template erases through its actual selected row and source captures.
The complete family theorem supplies only its smaller-target recursive callbacks. -/
theorem eraseStmt_print
    {path : List Nat} {n : Nat} {st : Program.Stmt Op} {s : TypeScript.Stmt} {declared : Nat}
    (hchild : ∀ path fam d (source : EffSelfCarrier Op fam) y,
      sizeOf y < sizeOf s → ReadableAt classes sig fam source d →
      TypedPrintsTo sig ann path d fam source (.expr y) →
      PrintsTo sig d fam source (.expr ((eraseT classes sig spell fam d y).getD y)))
    (hchildren : ∀ path fam d (source : EffSelfCarrier Op fam) ys,
      sizeOf ys < sizeOf s → ReadableAt classes sig fam source d →
      TypedPrintsTo sig ann path d fam source (.exprs ys) →
      PrintsTo sig d fam source (.exprs (eraseSpine classes sig spell fam d ys)))
    (hblock : ∀ path d (source : Stmts Op) ss,
      sizeOf ss < sizeOf s → ReadableAt classes sig .stmts source d →
      TypedPrintsTo sig ann path d .stmts source (.stmts ss) →
      PrintsTo sig d .stmts source (.stmts (eraseStmts classes sig spell d ss)))
    (printed : cata_stmt (typedAlg sig ann) st path n = .ok (s, declared))
    (readable : ReadableAt classes sig .stmt st n) :
    ∃ plain,
      (Templates.table.findSome? fun row => eraseStmtRow n s row
        (fun fam d y _ => (eraseT classes sig spell fam d y).getD y)
        (fun fam d ys _ => eraseSpine classes sig spell fam d ys)
        (fun d body _ => eraseStmts classes sig spell d body)) = some (plain, declared) ∧
      cata_stmt (printAlg sig) st n = .ok (plain, declared) := by
  obtain ⟨ctor, args, hview⟩ : ∃ ctor args, view .stmt st = (ctor, args) := ⟨_, _, rfl⟩
  have hbuild : build .stmt ctor args = some st := by
    have h := build_view .stmt st
    rwa [hview] at h
  have hsorts : argSorts .stmt ctor = some (args.map argSortOf) := by
    have h := argSorts_view .stmt st
    rwa [hview] at h
  have hp : tableLayer sig .stmt ctor
      (atAddress path (args.map (ArgF.fold (typedAlg sig ann))) 0) n = .ok (s, declared) := by
    have h := congrFun (congrFun (typed_cata_build sig ann .stmt ctor args st hbuild) path) n
    change cata_stmt (typedAlg sig ann) st path n =
      tableLayer sig .stmt ctor (atAddress path (args.map (ArgF.fold (typedAlg sig ann))) 0) n at h
    exact h.symm.trans printed
  obtain ⟨d, hd⟩ := readable
  change cata_stmt (readableAlg classes sig) st n = some d at hd
  have hdom : domLayer classes sig .stmt ctor
      (args.map (ArgF.fold (readableAlg classes sig))) n = some d := by
    have h := cata_build (domLayer classes sig) .stmt ctor args st hbuild
    simp only [cataFam] at h
    rw [show readableAlg classes sig = EffAlgebra.ofLayer (domLayer classes sig) from rfl, h] at hd
    exact hd
  obtain ⟨row, t, τ, hfind, hout, hτ, hinst, rfl⟩ := stmtPrint_inv hp
  have hfindSource : Templates.table.find? (fun r => r.selects .stmt ctor args) = some row := by
    simpa only [selects_atAddress, selects_fold] using hfind
  obtain ⟨row', t', hfind', hout', hr, hddecl⟩ := stmtDom_inv hdom
  have hfindSource' : Templates.table.find? (fun r => r.selects .stmt ctor args) = some row' := by
    simpa only [selects_fold] using hfind'
  have heq : row' = row := Option.some.inj (hfindSource'.symm.trans hfindSource)
  subst row'
  have hteq := RowOut.stmt.inj (hout'.symm.trans hout)
  subst t'
  subst d
  have hselected : row.selects .stmt ctor args = true := by
    have h := List.find?_some hfindSource
    exact h
  obtain ⟨hfamily, hctor⟩ := selects_fam_ctor hselected
  have hsortsRow : argSorts row.fam row.ctor = some (args.map argSortOf) := by
    rw [hfamily, hctor]
    exact hsorts
  have hsortsCtor : argSorts .stmt row.ctor = some (args.map argSortOf) := by
    rw [hctor]
    exact hsorts
  have hmem := List.mem_of_find?_eq_some hfindSource
  obtain ⟨k, hk, _, _⟩ := find?_index _ Templates.table row hfindSource
  obtain ⟨σ, hσ, hagree⟩ := matchStmt_of_instStmt n τ t s hinst
  let child := fun fam d y (_ : sizeOf y < sizeOf s) => (eraseT classes sig spell fam d y).getD y
  let children := fun fam d ys (_ : sizeOf ys < sizeOf s) => eraseSpine classes sig spell fam d ys
  let block := fun d ss (_ : sizeOf ss < sizeOf s) => eraseStmts classes sig spell d ss
  let child' := fun fam d y i (hy : (i, .expr y) ∈ σ) =>
    child fam d y (matchStmt_below n t s σ hσ (i, .expr y) hy)
  let children' := fun fam d ys i (hy : (i, .exprs ys) ∈ σ) =>
    children fam d ys (matchStmt_below n t s σ hσ (i, .exprs ys) hy)
  let block' := fun d ss i (hy : (i, .stmts ss) ∈ σ) =>
    block d ss (matchStmt_below n t s σ hσ (i, .stmts ss) hy)
  have hτrow : printArgs sig row.fam n row.out
      (atAddress path (args.map (ArgF.fold (typedAlg sig ann))) 0) 0 = .ok τ := by
    rw [hfamily, hout]
    exact hτ
  have hrrow : argsReadable classes sig row.fam n row.out (rowDaemon row)
      (args.map (ArgF.fold (readableAlg classes sig))) 0 = true := by
    rw [hfamily, hout]
    exact hr
  have hmatched : ∀ i ∈ row.out.holes, lookup σ i = lookup τ i := by
    intro i hi
    exact hagree i (by rwa [hout] at hi)
  have recursive : ∀ i fam source, args[i]? = some (.child fam source) →
      ∀ capture (member : (i, capture) ∈ σ),
      let depth := argDepth row.fam (.child fam) n (row.out.levelAt i)
      ReadableAt classes sig fam source depth →
      TypedPrintsTo sig ann (path ++ [(args.take i).countP isChildArg]) depth fam source capture →
      PrintsTo sig depth fam source
        (eraseCapture row (args.map argSortOf) n σ child' children' block' ⟨(i, capture), member⟩) := by
    intro i fam source hsource capture member depth hread htyped
    have hslot : (args.map argSortOf)[i]? = some (.child fam) := by
      simp only [List.getElem?_map, hsource, Option.map_some, argSortOf]
    cases capture with
    | expr y =>
      simpa only [eraseCapture, hslot, Option.getD_some, child'] using
        hchild _ fam depth source y (matchStmt_below n t s σ hσ (i, .expr y) member) hread htyped
    | exprs ys =>
      simpa only [eraseCapture, hslot, Option.getD_some, children'] using
        hchildren _ fam depth source ys (matchStmt_below n t s σ hσ (i, .exprs ys) member) hread htyped
    | stmts ss =>
      have hfam : fam = .stmts := by
        cases fam <;> simp only [TypedPrintsTo] at htyped ⊢
      subst fam
      simpa only [eraseCapture, hslot, Option.getD_some, block'] using
        hblock _ depth source ss (matchStmt_below n t s σ hσ (i, .stmts ss) member) hread htyped
    | _ => cases fam <;> cases htyped
  obtain ⟨υ, hυ, erasedAgree⟩ := eraseCaptures_printArgs sig row (args.map argSortOf) n σ
    child' children' block'
    (atAddress path (args.map (ArgF.fold (typedAlg sig ann))) 0)
    (args.map (ArgF.fold (printAlg sig)))
    (by simp only [length_atAddress, List.length_map]) τ hτrow
    (fun i hi => holesStmt_of_instStmt n τ t s hinst i (by rwa [hout] at hi))
    hmatched
    (source_printArgs_transport classes sig ann path row n args σ child' children' block' τ hτrow
      hmatched hrrow (source_child_hole_stmt hmem hselected hsortsRow hout) recursive)
  obtain ⟨plain, hplain⟩ := prints_upTo (classes := classes) (sig := sig)
    (cataFam sizeAlg .stmt st) .stmt st n t.declares (Nat.le_refl _) hd
  have hplainLayer : tableLayer sig .stmt ctor (args.map (ArgF.fold (printAlg sig))) n =
      .ok (plain, t.declares) := by
    have h := cata_build (tableLayer sig) .stmt ctor args st hbuild
    simp only [cataFam] at h
    rw [show printAlg sig = EffAlgebra.ofLayer (tableLayer sig) from rfl, h] at hplain
    exact hplain
  obtain ⟨plainRow, plainTpl, τplain, hfindPlain, houtPlain, hτplain, hinstPlain, _⟩ :=
    stmtPrint_inv hplainLayer
  have hfindPlainSource : Templates.table.find? (fun r => r.selects .stmt ctor args) = some plainRow := by
    simpa only [selects_fold] using hfindPlain
  have heqPlain : plainRow = row := Option.some.inj (hfindPlainSource.symm.trans hfindSource)
  subst plainRow
  have htplPlain := RowOut.stmt.inj (houtPlain.symm.trans hout)
  subst plainTpl
  rw [hfamily, hout] at hυ
  have hυeq : υ = τplain := Except.ok.inj (hυ.symm.trans hτplain)
  subst υ
  refine ⟨plain, ?_, hplain⟩
  refine findSome?_of_index _ _ k row (plain, t.declares) ?_ hk ?_
  · intro j hj rj hrj
    rcases apart_of_lt hrj hk hj with hne | hapart
    · have hn : rj.fam ≠ .stmt := by rwa [hfamily] at hne
      unfold eraseStmtRow
      simp only [hn, ↓reduceIte]
    · exact eraseStmtRow_earlier_none child children block hapart hout hinst
  · exact eraseStmtRow_inst n s row child children block hfamily hout hsortsCtor hσ hinstPlain
      (fun i hi => erasedAgree i (by rwa [hout]))

end Effect4.Codegen


/-!
The statement-list step of typed-print erasure, exact-codecs and R8.
The selected row preserves its declared count. The existing reader law checks that count
against the source environment transition; the tail uses the same depth and source address.
-/
set_option autoImplicit false
namespace Effect4.Codegen
open TypeScript Effect4.Program Template Templates
variable {Op : Type} {classes : Classes.Classes} {sig : Signature Op}
  {spell : String → List String → Option Op} {ann : List Nat → Option (List Ty)}

/-- The generated statement spine passes the head's declared count to its tail. -/
theorem typed_stmts_cons (st : Program.Stmt Op) (ss : Stmts Op) (path : List Nat) (n : Nat) :
    cata_stmts (typedAlg sig ann) (.cons st ss) path n =
      (cata_stmt (typedAlg sig ann) st (path ++ [0]) n).bind fun head =>
        (cata_stmts (typedAlg sig ann) ss (path ++ [1]) (n + head.2)).bind fun tail =>
          .ok (head.1 :: tail) := rfl

/-- Reconstruct the statement spine from its selected statement row and its smaller tail.
Its consumer is the well-founded family erasure theorem. -/
theorem eraseStmts_print_step (hl : LawfulSpelling sig spell) {m : Nat}
    (hstmt : ∀ path n (st : Program.Stmt Op) (s : TypeScript.Stmt) (declared : Nat),
      sizeOf s < m → ReadableAt classes sig .stmt st n →
      cata_stmt (typedAlg sig ann) st path n = .ok (s, declared) →
      ∃ plain,
        (Templates.table.findSome? fun row => eraseStmtRow n s row
          (fun fam d y _ => (eraseT classes sig spell fam d y).getD y)
          (fun fam d ys _ => eraseSpine classes sig spell fam d ys)
          (fun d body _ => eraseStmts classes sig spell d body)) = some (plain, declared) ∧
        cata_stmt (printAlg sig) st n = .ok (plain, declared))
    (htail : ∀ path n (ss : Stmts Op) (tail : List TypeScript.Stmt), sizeOf tail < m →
      ReadableAt classes sig .stmts ss n → TypedPrintsTo sig ann path n .stmts ss (.stmts tail) →
      PrintsTo sig n .stmts ss (.stmts (eraseStmts classes sig spell n tail))) :
    ∀ path n (ss : Stmts Op) (target : List TypeScript.Stmt), sizeOf target ≤ m →
      ReadableAt classes sig .stmts ss n → TypedPrintsTo sig ann path n .stmts ss (.stmts target) →
      PrintsTo sig n .stmts ss (.stmts (eraseStmts classes sig spell n target))
  | path, n, ss, target, hx, hr, hp => by
    cases ss with
    | nil =>
      simp only [TypedPrintsTo] at hp
      cases hp
      rw [eraseStmts]
      rfl
    | cons st ss =>
      simp only [TypedPrintsTo, typed_stmts_cons] at hp
      obtain ⟨⟨s, declared⟩, hs, hp⟩ := bind_eq_ok.mp hp
      obtain ⟨tail, htailPrinted, htarget⟩ := bind_eq_ok.mp hp
      cases htarget
      change sizeOf (s :: tail) ≤ m at hx
      obtain ⟨d, hd⟩ := hr
      simp only [cataFam, dom_stmts_cons, Option.bind_eq_some_iff] at hd
      obtain ⟨d1, hd1, d2, hd2, _⟩ := hd
      have hsize : sizeOf (s :: tail) = 1 + sizeOf s + sizeOf tail := List.cons.sizeOf_spec s tail
      obtain ⟨plain, hrow, hplain⟩ := hstmt (path ++ [0]) n st s declared (by omega) ⟨d1, hd1⟩ hs
      have hdecl : d1 = declared :=
        (readStmt_print (classes := classes) (sig := sig) (spell := spell)
          (m := sizeOf plain) (fun smaller _ => printsBackUpTo hl smaller)
          (Nat.le_refl _) hplain hd1).2
      subst d1
      have htailPlain := htail (path ++ [1]) (n + declared) ss tail (by omega) ⟨d2, hd2⟩ htailPrinted
      simp only [PrintsTo] at htailPlain ⊢
      rw [eraseStmts, hrow]
      simp only [cata_stmts_cons, hplain, htailPlain, ok_bind]
      rfl

end Effect4.Codegen


/-!
The existing table's fixed expression roots are unchanged by node annotation erasure.
These helpers serve the expression step of typed-print erasure, exact-codecs and R8.
They assert a finite table property, not a new source admission requirement.
-/
set_option autoImplicit false
namespace Effect4.Codegen
open TypeScript Effect4.Program Template Templates
variable {Op : Type}

theorem find_perform_row {R : EffFam → Type} (args : List (ArgF Op R)) :
    Templates.table.find? (fun row => row.selects .eff "perform" args) =
      some ⟨.eff, "perform", [], .rowCall⟩ := rfl

theorem typedLayer_template (sig : Signature Op) (ann : List Nat → Option (List Ty))
    {fam : EffFam} {ctor : String} {args : List (ArgF Op TCarrier)}
    {row : Templates.Row} {t : Tpl}
    (selected : Templates.table.find? (fun r => r.selects fam ctor args) = some row)
    (output : row.out = .tpl t) :
    typedLayer sig ann fam ctor args = fun path => tableLayer sig fam ctor (atAddress path args 0) := by
  unfold typedLayer
  split
  · have eq := Option.some.inj ((find_perform_row _).symm.trans selected)
    subst row
    cases output
  · rfl

theorem eraseNode_of_exprHead (n : Nat) (x : Expr) {head : String}
    (headed : exprHead? x = some head) : EraseTermTypes.eraseNode n x = x := by
  fun_cases EraseTermTypes.eraseNode n x
  all_goals simp only [exprHead?, reduceCtorEq] at headed
  all_goals rfl

def plainTemplateRoot (row : Templates.Row) : Bool :=
  match row.out with
  | .tpl t => !t.rigid || t.head?.isSome || match t with
    | .method _ _ _ => true
    | _ => false
  | _ => true

theorem table_plainTemplateRoot : Templates.table.all plainTemplateRoot = true := by decide

theorem eraseNode_of_table_inst {row : Templates.Row} (member : row ∈ Templates.table)
    {t : Tpl} (output : row.out = .tpl t) (rigid : t.rigid = true)
    {n : Nat} {τ : Subst} {x : Expr} (printed : inst n τ t = some x) :
    EraseTermTypes.eraseNode n x = x := by
  have shape := table_fact table_plainTemplateRoot member
  simp only [plainTemplateRoot, output, rigid, Bool.not_true, Bool.false_or,
    Bool.or_eq_true] at shape
  rcases shape with headed | method
  · obtain ⟨head, hhead⟩ := Option.isSome_iff_exists.mp headed
    exact eraseNode_of_exprHead n x (head_of_inst n τ t x printed hhead)
  · cases t <;> simp only [Bool.false_eq_true] at method
    rename_i target name args
    change ((inst n τ target).bind fun target' => (insts n τ args).bind fun args' =>
      some (.method target' name args')) = some x at printed
    obtain ⟨target', _, printed⟩ := Option.bind_eq_some_iff.mp printed
    obtain ⟨args', _, printed⟩ := Option.bind_eq_some_iff.mp printed
    have hx := Option.some.inj printed
    subst x
    rfl

end Effect4.Codegen


/-!
The rigid expression row erases through its actual source captures.
This helper serves the raw typed-print erasure law, exact-codecs and R8.
The callbacks are the smaller-target induction hypotheses.
-/
set_option autoImplicit false
namespace Effect4.Codegen
open TypeScript Effect4.Program Template Templates
variable {Op : Type} {classes : Classes.Classes} {sig : Signature Op}
  {spell : String → List String → Option Op} {ann : List Nat → Option (List Ty)}

set_option maxHeartbeats 2000000 in
theorem typed_child_at_hole {fam : EffFam} {n : Nat} {path : List Nat}
    {row : Templates.Row} {args : List (ArgF Op (EffSelfCarrier Op))}
    {t : Tpl} {τ : Subst} {x : Expr}
    (_output : row.out = .tpl t) (_family : row.fam = fam) (rigid : t.rigid = true)
    (printed : printArgs sig fam n (.tpl t)
      (atAddress path (args.map (ArgF.fold (typedAlg sig ann))) 0) 0 = .ok τ)
    (instantiated : inst n τ t = some x)
    (readable : argsReadable classes sig fam n (.tpl t) (rowDaemon row)
      (args.map (ArgF.fold (readableAlg classes sig))) 0 = true)
    (recursive : ∀ path fam d (source : EffSelfCarrier Op fam) y,
      sizeOf y < sizeOf x → ReadableAt classes sig fam source d →
      TypedPrintsTo sig ann path d fam source (.expr y) → nodeLike y = true)
    (i : Nat) (y : Expr) (child : childHole (args.map argSortOf) i = true)
    (hole : i ∈ holes t) (look : lookup τ i = some (.expr y)) : nodeLike y = true := by
  obtain ⟨σ, matched, agree⟩ := match_of_inst n τ t x instantiated
  have smaller := match_below n t x σ rigid matched (i, .expr y)
    (mem_of_lookup (by rw [agree i hole, look]))
  unfold childHole at child
  rw [List.getElem?_map] at child
  cases sourceAt : args[i]? with
  | none => rw [sourceAt] at child; exact absurd child Bool.false_ne_true
  | some source =>
    rw [sourceAt] at child
    have domain := argsReadable_at (args.map (ArgF.fold (readableAlg classes sig))) 0 i
      (ArgF.fold (readableAlg classes sig) source) readable
      (by simp only [List.getElem?_map, sourceAt, Option.map_some])
    rw [argSortOf_fold, Nat.zero_add] at domain
    cases source with
    | child childFam source =>
      have addressed := atAddress_fold_child sig ann path args i childFam source sourceAt
      have hp := (printArgs_lookup _ 0 τ printed).1 i _ addressed
      rw [Nat.zero_add, argSortOf, look] at hp
      exact recursive _ childFam _ source y smaller (readableAt_of_argReadable domain)
        (typedPrintsTo_of_printArg hp)
    | _ => exact absurd child Bool.false_ne_true

set_option maxHeartbeats 2000000 in
theorem eraseExprRow_source_rigid {fam : EffFam} {path : List Nat} {n : Nat}
    {args : List (ArgF Op (EffSelfCarrier Op))} {ctor : String}
    {row : Templates.Row} {t : Tpl} {τ : Subst} {x plain : Expr} {τplain : Subst}
    (member : row ∈ Templates.table) (selected : row.selects fam ctor args = true)
    (sorts : argSorts row.fam row.ctor = some (args.map argSortOf))
    (output : row.out = .tpl t) (rigid : t.rigid = true)
    (printed : printArgs sig row.fam n row.out
      (atAddress path (args.map (ArgF.fold (typedAlg sig ann))) 0) 0 = .ok τ)
    (instantiated : inst n τ t = some x)
    (readable : argsReadable classes sig row.fam n row.out (rowDaemon row)
      (args.map (ArgF.fold (readableAlg classes sig))) 0 = true)
    (ordinaryArgs : printArgs sig row.fam n row.out (args.map (ArgF.fold (printAlg sig))) 0 = .ok τplain)
    (ordinaryInst : inst n τplain t = some plain)
    (hchild : ∀ path fam d (source : EffSelfCarrier Op fam) y,
      sizeOf y < sizeOf x → ReadableAt classes sig fam source d →
      TypedPrintsTo sig ann path d fam source (.expr y) →
      PrintsTo sig d fam source (.expr ((eraseT classes sig spell fam d y).getD y)))
    (hchildren : ∀ path fam d (source : EffSelfCarrier Op fam) ys,
      sizeOf ys < sizeOf x → ReadableAt classes sig fam source d →
      TypedPrintsTo sig ann path d fam source (.exprs ys) →
      PrintsTo sig d fam source (.exprs (eraseSpine classes sig spell fam d ys)))
    (hblock : ∀ path d (source : Stmts Op) ss,
      sizeOf ss < sizeOf x → ReadableAt classes sig .stmts source d →
      TypedPrintsTo sig ann path d .stmts source (.stmts ss) →
      PrintsTo sig d .stmts source (.stmts (eraseStmts classes sig spell d ss))) :
    eraseExprRow classes sig spell fam n x row
      (fun fam d y _ => (eraseT classes sig spell fam d y).getD y)
      (fun fam d ys _ => eraseSpine classes sig spell fam d ys)
      (fun d body _ => eraseStmts classes sig spell d body)
      (fun fam' _ d => eraseT classes sig spell fam' d x) = some plain := by
  obtain ⟨family, constructor⟩ := selects_fam_ctor selected
  have sortsFam : argSorts fam row.ctor = some (args.map argSortOf) := by rwa [family] at sorts
  obtain ⟨σ, matched, agree⟩ := match_of_inst n τ t x instantiated
  let child := fun fam d y (_ : sizeOf y < sizeOf x) => (eraseT classes sig spell fam d y).getD y
  let children := fun fam d ys (_ : sizeOf ys < sizeOf x) => eraseSpine classes sig spell fam d ys
  let block := fun d ss (_ : sizeOf ss < sizeOf x) => eraseStmts classes sig spell d ss
  let child' := fun fam d y i (hy : (i, .expr y) ∈ σ) =>
    child fam d y (match_below n t x σ rigid matched (i, .expr y) hy)
  let children' := fun fam d ys i (hy : (i, .exprs ys) ∈ σ) =>
    children fam d ys (match_below n t x σ rigid matched (i, .exprs ys) hy)
  let block' := fun d ss i (hy : (i, .stmts ss) ∈ σ) =>
    block d ss (match_below n t x σ rigid matched (i, .stmts ss) hy)
  have hmatched : ∀ i ∈ row.out.holes, lookup σ i = lookup τ i := by
    intro i hi
    exact agree i (by rwa [output] at hi)
  have recursive : ∀ i fam source, args[i]? = some (.child fam source) →
      ∀ capture (member : (i, capture) ∈ σ),
      let depth := argDepth row.fam (.child fam) n (row.out.levelAt i)
      ReadableAt classes sig fam source depth →
      TypedPrintsTo sig ann (path ++ [(args.take i).countP isChildArg]) depth fam source capture →
      PrintsTo sig depth fam source
        (eraseCapture row (args.map argSortOf) n σ child' children' block' ⟨(i, capture), member⟩) := by
    intro i fam source sourceAt capture member depth hread htyped
    have hslot : (args.map argSortOf)[i]? = some (.child fam) := by
      simp only [List.getElem?_map, sourceAt, Option.map_some, argSortOf]
    cases capture with
    | expr y =>
      simpa only [eraseCapture, hslot, Option.getD_some, child'] using
        hchild _ fam depth source y (match_below n t x σ rigid matched (i, .expr y) member) hread htyped
    | exprs ys =>
      simpa only [eraseCapture, hslot, Option.getD_some, children'] using
        hchildren _ fam depth source ys (match_below n t x σ rigid matched (i, .exprs ys) member) hread htyped
    | stmts ss =>
      have hfam : fam = .stmts := by
        cases fam <;> simp only [TypedPrintsTo] at htyped ⊢
      subst fam
      simpa only [eraseCapture, hslot, Option.getD_some, block'] using
        hblock _ depth source ss (match_below n t x σ rigid matched (i, .stmts ss) member) hread htyped
    | _ => cases fam <;> cases htyped
  obtain ⟨υ, hυ, erasedAgree⟩ := eraseCaptures_printArgs sig row (args.map argSortOf) n σ
    child' children' block'
    (atAddress path (args.map (ArgF.fold (typedAlg sig ann))) 0)
    (args.map (ArgF.fold (printAlg sig)))
    (by simp only [length_atAddress, List.length_map]) τ printed
    (fun i hi => holes_of_inst n τ t x instantiated i (by rwa [output] at hi)) hmatched
    (source_printArgs_transport classes sig ann path row n args σ child' children' block' τ printed
      hmatched readable (source_child_hole member selected sorts output) recursive)
  have sameArgs : υ = τplain := Except.ok.inj (hυ.symm.trans ordinaryArgs)
  subst υ
  exact eraseExprRow_rigid_inst classes sig spell fam n x row child children block
    (fun fam' _ d => eraseT classes sig spell fam' d x) family output sortsFam matched rigid ordinaryInst
    (fun i hi => erasedAgree i (by rwa [output]))

end Effect4.Codegen


/-!
# Typed action image head

Placement: exact-codecs, R8; helper of the typed-print erasure claim.
Consumer: eraseT_print at the transparent eff-to-action row.
Reach: actual cata_action of typedAlg, at arbitrary annotation, address and depth.
The table owns the action root; child annotations remain arbitrary.
This helper changes no source syntax, admission or erasure premise.
It establishes no target compiler result or host execution.
-/

set_option autoImplicit false
namespace Effect4.Codegen
open TypeScript Effect4.Program Template Templates
variable {Op : Type} {classes : Classes.Classes} {sig : Signature Op}

/-- A typed action has an action head, even when its children carry arbitrary annotations.
The consumer retains ReadableAt, as the structural erasure statement requires. -/
theorem typed_action_image_head (ann : List Nat → Option (List Ty))
    {c : EffSelfCarrier Op .action} {path : List Nat} {d : Nat} {x : Expr}
    (printed : cata_action (typedAlg sig ann) c path d = .ok x)
    (_readable : ReadableAt classes sig .action c d) :
    ∃ h, exprHead? x = some h ∧ h ∈ actionHeads := by
  obtain ⟨ctor, args, hview⟩ : ∃ ctor args, view .action c = (ctor, args) := ⟨_, _, rfl⟩
  have hbuild : build .action ctor args = some c := by
    have h := build_view .action c
    rwa [hview] at h
  have hp : tableLayer.rowPrint sig .action ctor
      (atAddress path (args.map (ArgF.fold (typedAlg sig ann))) 0) d = .ok x := by
    have h := congrFun (congrFun (typed_cata_build sig ann .action ctor args c hbuild) path) d
    -- typedLayer's sole override is .eff/perform; an action uses the addressed table layer.
    change cata_action (typedAlg sig ann) c path d =
      tableLayer.rowPrint sig .action ctor
        (atAddress path (args.map (ArgF.fold (typedAlg sig ann))) 0) d at h
    exact h.symm.trans printed
  obtain ⟨row, hfind, hcase⟩ := rowPrint_inv hp
  have hmem := List.mem_of_find?_eq_some hfind
  have hfam : row.fam = .action := by
    have h := List.find?_some hfind
    exact (selects_fam_ctor h).1
  have hshape := table_fact table_actionHeaded hmem
  simp only [actionRowHeaded, hfam, bne_self_eq_false, Bool.false_or] at hshape
  rcases hcase with ⟨t, substitution, hout, _, hinst⟩ | ⟨_, _, hout, _, _⟩
  · rw [hout] at hshape
    simp only [Bool.and_eq_true, Option.any_eq_true] at hshape
    obtain ⟨_, h, hh, _⟩ := hshape
    exact ⟨h, head_of_inst d substitution t x hinst hh,
      mem_actionHeads hmem hfam hout hh⟩
  · rw [hout] at hshape
    cases hshape

end Effect4.Codegen


/-!
The expression node step reconstructs the ordinary print through the existing table.
This serves typed-print erasure, exact-codecs and R8.
The smaller-target and lower-family callbacks are the well-founded induction hypotheses.
-/
set_option autoImplicit false
namespace Effect4.Codegen
open TypeScript Effect4.Program Template Templates
variable {Op : Type} {classes : Classes.Classes} {sig : Signature Op}
  {spell : String → List String → Option Op} {ann : List Nat → Option (List Ty)}

theorem readable_expr_prints {fam : EffFam} {e : EffSelfCarrier Op fam} {n : Nat}
    (family : fam = .eff ∨ fam = .action ∨ fam = .layer)
    (readable : ReadableAt classes sig fam e n) :
    ∃ plain, PrintsTo sig n fam e (.expr plain) := by
  obtain ⟨d, hd⟩ := readable
  have h := prints_upTo (classes := classes) (sig := sig)
    (cataFam sizeAlg fam e) fam e n d (Nat.le_refl _) hd
  rcases family with rfl | rfl | rfl <;> exact h

set_option maxHeartbeats 4000000 in
theorem eraseT_print (lawful : LawfulSpelling sig spell)
    {fam : EffFam} {path : List Nat} {n : Nat} {e : EffSelfCarrier Op fam} {x : Expr}
    (hchild : ∀ path fam d (source : EffSelfCarrier Op fam) y,
      sizeOf y < sizeOf x → ReadableAt classes sig fam source d →
      TypedPrintsTo sig ann path d fam source (.expr y) →
      (∃ plain, eraseT classes sig spell fam d y = some plain ∧ PrintsTo sig d fam source (.expr plain)) ∧
        nodeLike y = true)
    (hchildren : ∀ path fam d (source : EffSelfCarrier Op fam) ys,
      sizeOf ys < sizeOf x → ReadableAt classes sig fam source d →
      TypedPrintsTo sig ann path d fam source (.exprs ys) →
      PrintsTo sig d fam source (.exprs (eraseSpine classes sig spell fam d ys)))
    (hblock : ∀ path d (source : Stmts Op) ss,
      sizeOf ss < sizeOf x → ReadableAt classes sig .stmts source d →
      TypedPrintsTo sig ann path d .stmts source (.stmts ss) →
      PrintsTo sig d .stmts source (.stmts (eraseStmts classes sig spell d ss)))
    (hsame : ∀ fam', famRank fam' < famRank fam → ∀ path d source,
      ReadableAt classes sig fam' source d → TypedPrintsTo sig ann path d fam' source (.expr x) →
      (∃ plain, eraseT classes sig spell fam' d x = some plain ∧ PrintsTo sig d fam' source (.expr plain)) ∧
        nodeLike x = true)
    (family : fam = .eff ∨ fam = .action ∨ fam = .layer)
    (typed : TypedPrintsTo sig ann path n fam e (.expr x))
    (readable : ReadableAt classes sig fam e n) :
    (∃ plain, eraseT classes sig spell fam n x = some plain ∧ PrintsTo sig n fam e (.expr plain)) ∧
      nodeLike x = true := by
  obtain ⟨ctor, args, hview⟩ : ∃ ctor args, view fam e = (ctor, args) := ⟨_, _, rfl⟩
  have hbuild : build fam ctor args = some e := by
    have h := build_view fam e
    rwa [hview] at h
  have hsorts : argSorts fam ctor = some (args.map argSortOf) := by
    have h := argSorts_view fam e
    rwa [hview] at h
  obtain ⟨plain, ordinary⟩ := readable_expr_prints family readable
  have hp : tableLayer.rowPrint sig fam ctor (args.map (ArgF.fold (printAlg sig))) n = .ok plain := by
    have h := cata_build (tableLayer sig) fam ctor args e hbuild
    rcases family with rfl | rfl | rfl <;> simp only [PrintsTo, cataFam] at ordinary h <;>
      (rw [show printAlg sig = EffAlgebra.ofLayer (tableLayer sig) from rfl, h] at ordinary; exact ordinary)
  have htyped := typed_cata_build sig ann fam ctor args e hbuild
  obtain ⟨d, hd⟩ := readable
  have hdom : domLayer.rowDom classes sig fam ctor (args.map (ArgF.fold (readableAlg classes sig))) n = some d := by
    have h := cata_build (domLayer classes sig) fam ctor args e hbuild
    rw [show readableAlg classes sig = EffAlgebra.ofLayer (domLayer classes sig) from rfl, h] at hd
    rcases family with rfl | rfl | rfl <;> exact hd
  obtain ⟨row, hfind, hcase⟩ := rowPrint_inv hp
  obtain ⟨row', hfind', hcase'⟩ := rowDom_inv hdom
  rw [find?_selects_fold (readableAlg classes sig) (printAlg sig), hfind, Option.some.injEq] at hfind'
  subst hfind'
  have hfindSource : Templates.table.find? (fun r => r.selects fam ctor args) = some row := by
    simpa only [selects_fold] using hfind
  obtain ⟨k, hk, _, _⟩ := find?_index _ Templates.table row hfindSource
  have hsel := List.find?_some hfindSource
  obtain ⟨hfamrow, hctor⟩ := selects_fam_ctor hsel
  have hmem := List.mem_of_getElem? hk
  have hshape := table_fact table_shape hmem
  have hsortsRow : argSorts row.fam row.ctor = some (args.map argSortOf) := by
    rw [hfamrow, hctor]
    exact hsorts
  have hsortsCtor : argSorts fam row.ctor = some (args.map argSortOf) := by rwa [hctor]
  have hother : ∀ j < k, ∀ rj, Templates.table[j]? = some rj → rj.fam ≠ fam ∨ rowsApart rj row = true :=
    fun j hj rj hrj => by rw [← hfamrow]; exact apart_of_lt hrj hk hj
  have childPlain : ∀ path fam d (source : EffSelfCarrier Op fam) y,
      sizeOf y < sizeOf x → ReadableAt classes sig fam source d →
      TypedPrintsTo sig ann path d fam source (.expr y) →
      PrintsTo sig d fam source (.expr ((eraseT classes sig spell fam d y).getD y)) := by
    intro path fam d source y smaller hr ht
    obtain ⟨plain, erased, printed⟩ := (hchild path fam d source y smaller hr ht).1
    rw [erased, Option.getD_some]
    exact printed
  rcases hcase with ⟨t, τplain, hout, hτplain, hinstplain⟩ | ⟨op, request, hout, hargs, hpplain⟩
  · rcases hcase' with ⟨t', hout', hr⟩ | ⟨_, _, hout', _⟩
    swap; · rw [hout] at hout'; cases hout'
    rw [hout, RowOut.tpl.injEq] at hout'
    subst hout'
    have hfindTyped : Templates.table.find? (fun r => r.selects fam ctor (args.map (ArgF.fold (typedAlg sig ann)))) = some row := by
      simpa only [selects_fold] using hfindSource
    have hpTyped : tableLayer.rowPrint sig fam ctor
        (atAddress path (args.map (ArgF.fold (typedAlg sig ann))) 0) n = .ok x := by
      rcases family with rfl | rfl | rfl <;> simp only [TypedPrintsTo, cataFam] at typed htyped <;>
        (rw [htyped, typedLayer_template sig ann hfindTyped hout] at typed; exact typed)
    obtain ⟨typedRow, hfindTypedRow, typedCase⟩ := rowPrint_inv hpTyped
    have hfindTypedSource : Templates.table.find? (fun r => r.selects fam ctor args) = some typedRow := by
      simpa only [selects_atAddress, selects_fold] using hfindTypedRow
    have typedRowEq : typedRow = row := Option.some.inj (hfindTypedSource.symm.trans hfindSource)
    subst typedRow
    rcases typedCase with ⟨t', τ, hout', hτ, hinst⟩ | ⟨_, _, hout', _⟩
    swap; · rw [hout] at hout'; cases hout'
    rw [hout, RowOut.tpl.injEq] at hout'
    subst hout'
    by_cases hrigid : t.rigid = true
    · have hnode := typed_child_at_hole hout hfamrow hrigid hτ hinst hr
        (fun path fam d source y smaller hr ht => (hchild path fam d source y smaller hr ht).2)
      have hnormal := eraseNode_of_table_inst hmem hout hrigid hinst
      refine ⟨⟨plain, eraseT_of_row hnormal hk (fun j hj rj hrj => ?_) ?_, ordinary⟩, ?_⟩
      · rcases hother j hj rj hrj with hne | apart
        · exact eraseExprRow_none_of_fam hne
        · exact erase_earlier_none_rigid apart hout hrigid hsortsRow hinst hnode
      · exact eraseExprRow_source_rigid hmem hsel hsortsRow hout hrigid
          (by rw [hfamrow, hout]; exact hτ) hinst (by rw [hfamrow, hout]; exact hr)
          (by rw [hfamrow, hout]; exact hτplain) hinstplain childPlain hchildren hblock
      · have htop : t.nodeTop = true := by
          rcases family with rfl | rfl | rfl <;>
            simpa only [rowShape, hfamrow, hout, hrigid, ↓reduceIte] using hshape
        exact inst_nodeLike n τ t x htop hinst
    · cases t with
      | hole i =>
        have hkind : (fam = .eff ∧ args.map argSortOf = [.child .action]) ∨
            (fam = .layer ∧ args.map argSortOf = [.path]) := by
          unfold rowShape at hshape
          rw [hfamrow, hout] at hshape
          rcases family with rfl | rfl | rfl <;>
            simp only [Tpl.rigid, Bool.false_eq_true, ↓reduceIte, hsortsCtor, Bool.or_eq_true,
              Bool.and_eq_true, beq_iff_eq, beq_self_eq_true, Option.some.injEq, true_and,
              reduceCtorEq, false_and, or_false, false_or] at hshape <;> aesop
        rcases family with rfl | rfl | rfl
        · have hact : args.map argSortOf = [.child .action] := by
            rcases hkind with ⟨_, h⟩ | ⟨h, _⟩
            · exact h
            · cases h
          obtain ⟨a, rfl, ha⟩ := args_of_sorts_single hact
          have hi := hole_zero hmem hout (s := .child .action) (by rw [hsortsRow, hact])
          subst hi
          cases a with
          | child fam' source =>
            simp only [argSortOf, ArgSort.child.injEq] at ha
            subst ha
            have hp0 := (printArgs_lookup _ 0 τ hτ).1 0
              (.child .action (cata_action (typedAlg sig ann) source (path ++ [0]))) rfl
            simp only [inst] at hinst
            have hlook : lookup τ 0 = some (.expr x) := by
              revert hinst; cases lookup τ 0 <;> aesop
            rw [Nat.add_zero, argSortOf, hlook] at hp0
            have hpa := typedPrintsTo_of_printArg hp0
            have hlevel : (RowOut.tpl (.hole 0)).levelAt 0 = 0 := rfl
            rw [hlevel] at hpa
            have hra : ReadableAt classes sig .action source (argDepth .eff (.child .action) n 0) := by
              have h := argsReadable_at _ 0 0 (ArgF.fold (readableAlg classes sig) (.child .action source)) hr rfl
              rw [Nat.add_zero, argSortOf_fold, argSortOf, hlevel] at h
              exact readableAt_of_argReadable h
            have lower : famRank .action < famRank .eff := by decide
            obtain ⟨⟨erased, herase, hplain⟩, hnode⟩ := hsame .action lower _ _ source hra hpa
            obtain ⟨head, hhead, haction⟩ := typed_action_image_head ann hpa hra
            have normal := eraseNode_of_exprHead n x hhead
            have hplainEq : erased = plain := by
              have oldp := (printArgs_lookup _ 0 τplain hτplain).1 0
                (ArgF.fold (printAlg sig) (.child .action source)) rfl
              have oldlook : lookup τplain 0 = some (.expr plain) := by
                simp only [inst] at hinstplain
                revert hinstplain; cases lookup τplain 0 <;> aesop
              rw [Nat.add_zero, argSortOf_fold, argSortOf, oldlook, hlevel] at oldp
              have old := printsTo_of_printArg oldp
              exact Except.ok.inj (hplain.symm.trans old)
            subst erased
            refine ⟨⟨plain, eraseT_of_row normal hk (fun j hj rj hrj => ?_) ?_, ordinary⟩, hnode⟩
            · rcases hother j hj rj hrj with hne | apart
              · exact eraseExprRow_none_of_fam hne
              · exact erase_earlier_none_action apart hout (by rw [hsortsRow, hact]) hhead haction
            · simp only [eraseExprRow, hfamrow, hout, ↓reduceIte,
                show argSorts .eff row.ctor = some [.child .action] from by rw [hsortsCtor, hact],
                Tpl.rigid, Bool.false_eq_true, ↓reduceDIte, lower, herase]
              rfl
          | _ => cases ha
        · rcases hkind with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h
        · have hpath : args.map argSortOf = [.path] := by
            rcases hkind with ⟨h, _⟩ | ⟨_, h⟩
            · cases h
            · exact h
          obtain ⟨a, rfl, ha⟩ := args_of_sorts_single hpath
          have hi := hole_zero hmem hout (s := .path) (by rw [hsortsRow, hpath])
          subst hi
          cases a with
          | path p =>
            have hp0 := (printArgs_lookup _ 0 τ hτ).1 0 (.path p) rfl
            simp only [Nat.add_zero, printArg, Except.ok.injEq] at hp0
            have hx : x = .ident (LayerTerm.refName p) := by
              simp only [inst] at hinst
              rw [← hp0] at hinst
              exact (Option.some.inj hinst).symm
            have hpplain := (printArgs_lookup _ 0 τplain hτplain).1 0 (.path p) rfl
            simp only [Nat.add_zero, printArg, Except.ok.injEq] at hpplain
            have hplain : plain = .ident (LayerTerm.refName p) := by
              simp only [inst] at hinstplain
              rw [← hpplain] at hinstplain
              exact (Option.some.inj hinstplain).symm
            have normal : EraseTermTypes.eraseNode n x = x := by rw [hx]; rfl
            refine ⟨⟨plain, eraseT_of_row normal hk (fun j hj rj hrj => ?_) ?_, ordinary⟩, ?_⟩
            · rcases hother j hj rj hrj with hne | apart
              · exact eraseExprRow_none_of_fam hne
              · exact erase_earlier_none_path apart hout (by rw [hsortsRow, hpath]) hx
            · rw [hx, hplain]
              simp only [eraseExprRow, hfamrow, hout, ↓reduceIte,
                show argSorts .layer row.ctor = some [.path] from by rw [hsortsCtor, hpath],
                Tpl.rigid, Bool.false_eq_true, ↓reduceDIte]
              rfl
            · rw [hx]; rfl
          | _ => cases ha
      | _ => exact absurd rfl hrigid
  · rcases hcase' with ⟨_, hout', _⟩ |
      ⟨op', request', hout', hargs', hd', hreq, hcover, hun, htypes, hterm⟩
    · rw [hout] at hout'; cases hout'
    have hfamily := table_fact table_family hmem
    simp only [rowFamily, hout, beq_iff_eq] at hfamily
    rw [hfamily] at hfamrow
    subst hfamrow
    have sourceArgs := fold_eq_op_term (printAlg sig) hargs
    have domainArgs := fold_eq_op_term (readableAlg classes sig) hargs'
    rw [sourceArgs, List.cons.injEq, List.cons.injEq, ArgF.op.injEq, ArgF.term.injEq] at domainArgs
    obtain ⟨rfl, rfl, _⟩ := domainArgs
    have he : e = .perform op request := eff_of_view_op_term e op request (by rw [hview]; exact sourceArgs)
    subst e
    change printPerformAt sig n op request (ann path) = .ok x at typed
    obtain ⟨ordinaryCall, hpCall, atRow⟩ := eraseExprRow_printPerformAt lawful hd' hreq hcover hun htypes hterm
      typed row hfamily hout
      (fun fam d y _ => (eraseT classes sig spell fam d y).getD y)
      (fun fam d ys _ => eraseSpine classes sig spell fam d ys)
      (fun d ss _ => eraseStmts classes sig spell d ss)
      (fun fam' _ d => eraseT classes sig spell fam' d x)
    have heq : ordinaryCall = plain := Except.ok.inj (hpCall.symm.trans hpplain)
    subst ordinaryCall
    refine ⟨⟨plain, eraseT_of_row (TypedRowShapeSupport.eraseNode_printPerformAt lawful typed n) hk
        (fun j hj rj hrj => ?_) atRow, hpplain⟩,
      TypedRowShapeSupport.printPerformAt_nodeLike typed⟩
    rcases hother j hj rj hrj with hne | apart
    · exact eraseExprRow_none_of_fam hne
    · exact erase_earlier_none_rowCall apart hout
        (fun t head headed reserved => TypedRowShapeSupport.printPerformAt_no_reserved lawful typed n t head headed reserved)
        (fun _ d => TypedRowShapeSupport.eraseT_action_none_of_printPerformAt lawful typed d)

end Effect4.Codegen


/-!
The raw successful typed print erases to today's print.
This closes the proposed typed-print erasure claim, exact-codecs and R8.
Reach: the existing readable fragment and lawful spelling, with arbitrary row annotations.
Success supplies row-owned-argument eligibility; no global spelling exclusion is added.
The existing reader's retraction and exactness laws then transport through named erasure.
This states no TypeScript typing or host execution agreement.
-/
set_option autoImplicit false
namespace Effect4.Codegen
open TypeScript Effect4.Program Template Templates
variable {Op : Type} {classes : Classes.Classes} {sig : Signature Op}
  {spell : String → List String → Option Op} {ann : List Nat → Option (List Ty)}

def TypedErasesUpTo (classes : Classes.Classes) (sig : Signature Op)
    (spell : String → List String → Option Op) (ann : List Nat → Option (List Ty)) (m : Nat) : Prop :=
  (∀ fam path n (e : EffSelfCarrier Op fam) (x : Expr), sizeOf x ≤ m →
    ReadableAt classes sig fam e n → TypedPrintsTo sig ann path n fam e (.expr x) →
    (∃ plain, eraseT classes sig spell fam n x = some plain ∧ PrintsTo sig n fam e (.expr plain)) ∧
      nodeLike x = true) ∧
  (∀ fam path n (e : EffSelfCarrier Op fam) (xs : List Expr), sizeOf xs ≤ m →
    ReadableAt classes sig fam e n → TypedPrintsTo sig ann path n fam e (.exprs xs) →
    PrintsTo sig n fam e (.exprs (eraseSpine classes sig spell fam n xs))) ∧
  (∀ path n (e : Stmts Op) (ss : List TypeScript.Stmt), sizeOf ss ≤ m →
    ReadableAt classes sig .stmts e n → TypedPrintsTo sig ann path n .stmts e (.stmts ss) →
    PrintsTo sig n .stmts e (.stmts (eraseStmts classes sig spell n ss)))

theorem eraseT_print_step (lawful : LawfulSpelling sig spell) {m : Nat}
    (ih : ∀ smaller, smaller < m → TypedErasesUpTo classes sig spell ann smaller)
    {fam : EffFam} {path : List Nat} {n : Nat} {e : EffSelfCarrier Op fam} {x : Expr}
    (size : sizeOf x ≤ m)
    (same : ∀ fam', famRank fam' < famRank fam → ∀ path d source,
      ReadableAt classes sig fam' source d → TypedPrintsTo sig ann path d fam' source (.expr x) →
      (∃ plain, eraseT classes sig spell fam' d x = some plain ∧ PrintsTo sig d fam' source (.expr plain)) ∧
        nodeLike x = true)
    (readable : ReadableAt classes sig fam e n)
    (typed : TypedPrintsTo sig ann path n fam e (.expr x)) :
    (∃ plain, eraseT classes sig spell fam n x = some plain ∧ PrintsTo sig n fam e (.expr plain)) ∧
      nodeLike x = true := by
  have family : fam = .eff ∨ fam = .action ∨ fam = .layer := by
    cases fam <;> simp only [TypedPrintsTo] at typed ⊢ <;> aesop
  exact eraseT_print lawful
    (fun path fam d source y smaller hr hp =>
      (ih (sizeOf y) (by omega)).1 fam path d source y (Nat.le_refl _) hr hp)
    (fun path fam d source ys smaller hr hp =>
      (ih (sizeOf ys) (by omega)).2.1 fam path d source ys (Nat.le_refl _) hr hp)
    (fun path d source ss smaller hr hp =>
      (ih (sizeOf ss) (by omega)).2.2 path d source ss (Nat.le_refl _) hr hp)
    same family typed readable

theorem typedErasesUpTo (lawful : LawfulSpelling sig spell) (m : Nat) :
    TypedErasesUpTo classes sig spell ann m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    have low : ∀ fam, famRank fam = 0 → ∀ path n (e : EffSelfCarrier Op fam) x,
        sizeOf x ≤ m → ReadableAt classes sig fam e n → TypedPrintsTo sig ann path n fam e (.expr x) →
        (∃ plain, eraseT classes sig spell fam n x = some plain ∧ PrintsTo sig n fam e (.expr plain)) ∧
          nodeLike x = true :=
      fun fam rank path n e x size hr hp =>
        eraseT_print_step lawful ih size (fun fam' lower => absurd lower (by omega)) hr hp
    refine ⟨fun fam path n e x size hr hp => ?_, ?_, ?_⟩
    · exact eraseT_print_step lawful ih size
        (fun fam' lower path d source hr' hp' =>
          low fam' (by have h := famRank_le_one fam; omega) path d source x size hr' hp') hr hp
    · exact eraseSpine_print_step
        (fun fam path n e y smaller hr hp =>
          ((ih (sizeOf y) smaller).1 fam path n e y (Nat.le_refl _) hr hp).1)
        (fun fam path n e ys smaller hr hp =>
          (ih (sizeOf ys) smaller).2.1 fam path n e ys (Nat.le_refl _) hr hp)
    · apply eraseStmts_print_step lawful
      · intro path n st s declared smaller hr hp
        exact eraseStmt_print
          (fun path fam d source y smaller' hr' hp' => by
            obtain ⟨plain, erased, printed⟩ :=
              ((ih (sizeOf y) (by omega)).1 fam path d source y (Nat.le_refl _) hr' hp').1
            rw [erased, Option.getD_some]
            exact printed)
          (fun path fam d source ys smaller' hr' hp' =>
            (ih (sizeOf ys) (by omega)).2.1 fam path d source ys (Nat.le_refl _) hr' hp')
          (fun path d source ss smaller' hr' hp' =>
            (ih (sizeOf ss) (by omega)).2.2 path d source ss (Nat.le_refl _) hr' hp') hp hr
      · exact fun path n e ss smaller hr hp =>
          (ih (sizeOf ss) smaller).2.2 path n e ss (Nat.le_refl _) hr hp

/-- The successful raw typed printer erases exactly to the existing ordinary printer.
The reader fragment and spelling laws remain the original premises (exact-codecs, R8). -/
@[semantics "exact-codecs" (requirement := R8)]
theorem eraseJoinArgs_printTypedAt (lawful : LawfulSpelling sig spell) {n : Nat} {e : Eff Op}
    (readable : Readable classes sig n e = true) {x : Expr}
    (printed : printTypedAt sig ann n e = .ok x) :
    print sig n e = .ok (eraseJoinArgs classes sig spell n x) := by
  obtain ⟨plain, erased, ordinary⟩ :=
    ((typedErasesUpTo (ann := ann) lawful (sizeOf x)).1 .eff [] n e x (Nat.le_refl _)
      (by unfold ReadableAt; simpa only [Readable, cataFam, Option.isSome_iff_exists] using readable)
      printed).1
  simp only [eraseJoinArgs, erased, Option.getD_some]
  exact ordinary

/-- The existing reader reads a successful raw typed print after named join erasure.
This carries the ordinary reader's retraction law on its existing fragment (exact-codecs, R8). -/
@[semantics "exact-codecs" (requirement := R8)]
theorem readTyped_printTypedAt (lawful : LawfulSpelling sig spell) {n : Nat} {e : Eff Op}
    (readable : Readable classes sig n e = true) {x : Expr}
    (printed : printTypedAt sig ann n e = .ok x) : readTyped classes sig spell n x = .ok e :=
  read_print lawful readable (eraseJoinArgs_printTypedAt lawful readable printed)

end Effect4.Codegen
