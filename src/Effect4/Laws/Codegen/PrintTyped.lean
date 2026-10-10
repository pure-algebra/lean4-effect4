import Effect4.Codegen.PrintTyped
import Effect4.Codegen.PrintEliminators
import Effect4.Laws.Program.Typing.Call
import Effect4.Laws.Program.Typing.Focus
import Effect4.Codegen.EraseTypes
import Effect4.Laws.Codegen.ReadPrint
import Effect4.Laws.Codegen.PrintReadable
import Effect4.Laws.Program.Typing.Annotate
import Effect4.Laws.Program.Address
import Effect4.Program.Binders

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
  obtain ⟨noRows, noSites⟩ := noJoin
  have annotation : typeArgsAt s env0 p = fun _ => none := by
    funext path
    unfold typeArgsAt
    rw [noRows path]
    rfl
  have sites : Effect4.Codegen.PrintEliminators.needsSitesAt s (annotate s env0 p) p = false := by
    apply List.any_eq_false.mpr
    intro path _
    exact fun hit => Bool.noConfusion ((noSites path).symm.trans hit)
  simp only [printTyped, sites, Bool.false_eq_true, ↓reduceIte, annotation]
  exact Effect4.Codegen.Templates.printTypedAt_none s env0.length p

end Effect4.Program

namespace Effect4.Codegen

open TypeScript
open Effect4.Program

variable {Op : Type} {classes : Classes.Classes} {sig : Signature Op}
  {spell : String → List RowArg → Option Op}

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
    eraseTerm n (.lambda ps body ret) = .lambda ps (eraseTerm (n + ps.length) body) ret :=
  mapCalls_lambda callInverse ps body ret n

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
    simp only [callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, ite_self, eraseCauseTermJoin]
  | some annotation =>
    have notTuple : ("recordValue" : String) ≠ "tuple" := by decide
    have notPair : ("recordValue" : String) ≠ "pair" := by decide
    simp only [Record.writeRecord, htarget, ht, eraseTerm_call, eraseTerm_generic,
      eraseTerm_ident, List.map_cons, List.map_nil, eraseTerm_writeTy, eraseTerm_objectProperties]
    simp only [callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, eraseCauseTermJoin, notTuple, notPair, ↓reduceIte, ite_self]

theorem eraseTerm_field (n : Nat) (optional : Bool) (key : String) (value : Expr) :
    eraseTerm n (Record.writeField optional key value) =
      Record.writeField optional key (eraseTerm n value) := by
  cases optional with
  | false =>
    simp only [Record.writeField, Bool.false_eq_true, ↓reduceIte, eraseTerm_call,
      eraseTerm_generic, eraseTerm_ident, List.map_cons, List.map_nil, eraseTerm_str]
    simp only [callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, ite_self, eraseCauseTermJoin]
  | true =>
    simp only [Record.writeField, ↓reduceIte, eraseTerm_call,
      eraseTerm_generic, eraseTerm_ident, List.map_cons, List.map_nil, eraseTerm_str]
    simp only [callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, ite_self, eraseCauseTermJoin]

theorem eraseTerm_set (n : Nat) (key : String) (receiver value : Expr) :
    eraseTerm n (Record.writeSet key receiver value) =
      Record.writeSet key (eraseTerm n receiver) (eraseTerm n value) := by
  simp only [Record.writeSet, eraseTerm_call, eraseTerm_generic,
    eraseTerm_ident, List.map_cons, List.map_nil, eraseTerm_str]
  simp only [callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, ite_self, eraseCauseTermJoin]

theorem eraseTerm_tupleAt (n index : Nat) (receiver : Expr) :
    eraseTerm n (Tuple.writeAt index receiver) = Tuple.writeAt index (eraseTerm n receiver) := by
  simp only [Tuple.writeAt, eraseTerm_call, eraseTerm_generic,
    eraseTerm_ident, List.map_cons, List.map_nil, eraseTerm_str]
  simp only [callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, ite_self, eraseCauseTermJoin]

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
    simp only [callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, ↓reduceIte, eraseCauseTermJoin]
  | some stored =>
    simp only [ListFold.write, Binders.write, eraseTerm_call, eraseTerm_generic,
      eraseTerm_ident, eraseTerm_lambda, Template.params, List.map_cons, List.map_nil,
      List.length_cons, List.length_nil, Nat.add_zero]
    simp only [callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, ↓reduceIte, eraseCauseTermJoin]

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
      | decls value =>
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
  {spell : String → List RowArg → Option Op}
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

/-- A step of typed-print-erasure: product annotation removal keeps the call shape.
Consumer: callInverse_call, then the shared term fold's erasure certificate. -/
theorem eraseProductJoin_hasCall (x : Expr) (input : ∃ head args, x = .call head args) :
    ∃ head args, eraseProductJoin x = .call head args := by
  fun_cases eraseProductJoin x <;> aesop

theorem eraseProductJoin_call (head : Expr) (args : List Expr) :
    ∃ head' args', eraseProductJoin (.call head args) = .call head' args' :=
  eraseProductJoin_hasCall (.call head args) ⟨head, args, rfl⟩

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
  obtain ⟨productHead, productArgs, hproduct⟩ := eraseProductJoin_call head args
  obtain ⟨firstHead, firstArgs, hfirst⟩ := eraseRecordJoin_call productHead productArgs
  obtain ⟨secondHead, secondArgs, hsecond⟩ := eraseFoldJoin_call n firstHead firstArgs
  obtain ⟨lastHead, lastArgs, hlast⟩ := eraseCauseTermJoin_call secondHead secondArgs
  exact ⟨lastHead, lastArgs, by rw [callInverse, hproduct, hfirst, hsecond, hlast]⟩

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
    | nil => simp only [printTerms, List.map_nil, callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, ↓reduceIte, eraseCauseTermJoin]
    | cons first rest =>
      cases rest with
      | nil => simp only [printTerms, List.map_cons, List.map_nil, callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, ↓reduceIte, eraseCauseTermJoin]
      | cons second rest =>
        cases rest with
        | nil => simp only [printTerms, List.map_cons, List.map_nil, callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, ↓reduceIte, eraseCauseTermJoin]
        | cons third rest =>
          cases rest with
          | cons fourth tail => simp only [printTerms, List.map_cons, callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, ↓reduceIte, eraseCauseTermJoin]
          | nil =>
            have hnl := eraseTerm_printTerm_not_lambda n third
            cases ht : eraseTerm n (printTerm n third) <;>
              simp only [printTerms, List.map_cons, List.map_nil, ht, callInverse, eraseProductJoin,
                eraseRecordJoin, eraseFoldJoin, ↓reduceIte, eraseCauseTermJoin]
            aesop
  · simp only [callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, hname, ↓reduceIte, eraseCauseTermJoin]

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
    simp only [callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, ite_self, eraseCauseTermJoin]
  h_cause_die t := by
    funext n
    simp only [eraseCause, printCause, rawCauseAlg, eraseTerm_call, eraseTerm_ident,
      List.map_cons, List.map_nil, eraseTerm_printTerm_identity]
    simp only [callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, ite_self, eraseCauseTermJoin]
  h_cause_interrupt who := by
    funext n
    cases who <;>
      simp only [eraseCause, printCause, rawCauseAlg, Option.toList_none, Option.toList_some,
        List.map_cons, List.map_nil, eraseTerm_call, eraseTerm_ident, eraseTerm_printTerm_identity] <;>
      simp only [callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, ite_self, eraseCauseTermJoin]
  h_cause_both left right := by
    funext n
    simp only [eraseCause, printCause, rawCauseAlg, eraseTerm_call, eraseTerm_ident,
      List.map_cons, List.map_nil]
    simp only [callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, ite_self, eraseCauseTermJoin]

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
  | decls value => cases printed
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

theorem eraseTerm_trailing (n : Nat) (args : List RowArg) :
    (args.map RowArg.print).map (EraseTermTypes.eraseTerm n) = args.map RowArg.print := by
  induction args with
  | nil => rfl
  | cons a rest ih =>
    rw [List.map_cons, List.map_cons, ih]
    cases a <;> rfl

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
    (spell : String → List RowArg → Option Op) (fam : EffFam) (n : Nat) (x : Expr)
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
  have hinst := Effect4.Program.inst_congr n _ τ t agree
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
  have hinst := Effect4.Program.instStmt_congr n _ τ t agree
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
  {spell : String → List RowArg → Option Op}

theorem splitHeadTypes_bare_none {x bare : Expr} {targets : List TypeRef}
    (h : splitHeadTypes x = some (bare, targets)) : splitHeadTypes bare = none := by
  unfold splitHeadTypes at h
  split at h <;> cases h <;> rfl

/-- Reading a bare call as an operation that carries no arguments excludes a typed head.
The row inverse consumes this refusal; the original reader remains unchanged. -/
theorem readCall_zero_excludes_head {n : Nat} {x bare : Expr} {targets : List TypeRef}
    {op : Op} {r : Term} (hsplit : splitHeadTypes x = some (bare, targets))
    (hbare : readCall classes sig spell n bare = .ok (.perform op r))
    (hnil : sig.typeArgsOf op = []) :
    ∃ why, readCall classes sig spell n x = .error why := by
  have hnone := splitHeadTypes_bare_none hsplit
  have hne := Effect4.Program.splitHeadTypes_ne_nil hsplit
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
  {spell : String → List RowArg → Option Op} {fam : EffFam} {n k : Nat}
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
  | decls value => rfl
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
  {spell : String → List RowArg → Option Op}

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
    (hbare : ∀ name args, x = .call (.ident name) args → name ∉ reserved)
    (hnot : ∀ name types args, x = .call (.generic (.ident name) types) args → name ∉ reserved)
    (d : Nat) : EraseTermTypes.eraseNode d x = x := by
  have optionReserved : "optionCase" ∈ reserved := by decide
  have scopedReserved : "Effect.scoped" ∈ reserved := by decide
  have acquireReserved : "Effect.acquireRelease" ∈ reserved := by decide
  have forkInReserved : "Effect.forkIn" ∈ reserved := by decide
  have tagReserved : ∀ name ∈ ["caseTag", "caseTagR"], name ∈ reserved := by
    intro name member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  have fiberReserved : ∀ name ∈ ["Fiber.join", "Fiber.await", "Fiber.interrupt"], name ∈ reserved := by
    intro name member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  have pairReserved : ∀ name ∈ ["Fiber.runIn", "Scope.close"], name ∈ reserved := by
    intro name member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  have forkReserved : ∀ name ∈
      ["Effect.forkChild", "Effect.forkDetach", "Effect.forkScoped", "Fiber.interruptAllAs"],
      name ∈ reserved := by
    intro name member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  have listReserved : ∀ name ∈ ["Fiber.interruptAll", "Fiber.awaitAll"], name ∈ reserved := by
    intro name member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  fun_cases EraseTermTypes.eraseNode d x
  · exact False.elim ((hbare "Effect.withFiber" _ rfl) (by decide))
  all_goals clear hbare
  all_goals aesop (add norm simp [List.contains_eq_mem, decide_eq_true_eq, Bool.and_eq_true],
    safe forward [tagReserved, fiberReserved, pairReserved, forkReserved, listReserved])

/-- A successful typed row keeps every node-level argument at every eraser depth.
This follows from actual row spelling ownership and the existing reserved-head separation. -/
theorem eraseNode_printPerformAt (hl : LawfulSpelling sig spell) {n : Nat} {op : Op}
    {r : Term} {annotation : Option (List Ty)} {x : Expr}
    (hp : Templates.printPerformAt sig n op r annotation = .ok x) (d : Nat) :
    EraseTermTypes.eraseNode d x = x := by
  have hs := printPerformAt_rowHeadOwned hp
  apply eraseNode_of_genericHead_not_reserved
  · intro name args heq
    rw [hs.1 name args heq]
    exact hl.spelling_not_reserved op
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
  {spell : String → List RowArg → Option Op}

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
  {spell : String → List RowArg → Option Op} {ann : List Nat → Option (List Ty)}

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
  {spell : String → List RowArg → Option Op} {ann : List Nat → Option (List Ty)}

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
  {spell : String → List RowArg → Option Op} {ann : List Nat → Option (List Ty)}

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

theorem eraseNode_of_exprHead_except_runIn (n : Nat) (x : Expr) {head : String}
    (headed : exprHead? x = some head) (other : head ≠ "Effect.withFiber") :
    EraseTermTypes.eraseNode n x = x := by
  fun_cases EraseTermTypes.eraseNode n x
  all_goals simp only [exprHead?, reduceCtorEq] at headed
  all_goals aesop (add safe forward [other])

def rawRunInTpl : Tpl :=
  .call (.ident "Effect.withFiber")
    (.cons (.arrowBlock []
      (.cons (.exprStmt (.call (.ident "Fiber.runIn")
        (.cons (.hole 0) (.cons (.hole 1) .nil))))
        (.cons (.ret (.ident "Effect.void")) .nil))) .nil)

def isRawRunInTpl : Tpl → Bool
  | .call (.ident "Effect.withFiber")
      (.cons (.arrowBlock []
        (.cons (.exprStmt (.call (.ident "Fiber.runIn")
          (.cons (.hole 0) (.cons (.hole 1) .nil))))
          (.cons (.ret (.ident "Effect.void")) .nil))) .nil) => true
  | _ => false

def rawWithFiberRow (row : Templates.Row) : Bool :=
  match row.out with
  | .tpl t => if t.head? == some "Effect.withFiber" then isRawRunInTpl t else true
  | _ => true

theorem table_rawWithFiberRow : Templates.table.all rawWithFiberRow = true := by decide

theorem rawRunInTpl_of_head {row : Templates.Row} (member : row ∈ Templates.table)
    {t : Tpl} (output : row.out = .tpl t) (headed : t.head? = some "Effect.withFiber") :
    t = rawRunInTpl := by
  have shape := table_fact table_rawWithFiberRow member
  unfold rawWithFiberRow at shape
  simp only [output] at shape
  rw [headed] at shape
  change isRawRunInTpl t = true at shape
  unfold isRawRunInTpl at shape
  split at shape
  · rfl
  · cases shape

theorem eraseNode_rawRunIn (n : Nat) (receiver scope : Expr) :
    EraseTermTypes.eraseNode n (.call (.ident "Effect.withFiber")
      [.arrowBlock [] [.exprStmt (.call (.ident "Fiber.runIn") [receiver, scope]),
        .ret (.ident "Effect.void")] none]) =
    .call (.ident "Effect.withFiber")
      [.arrowBlock [] [.exprStmt (.call (.ident "Fiber.runIn") [receiver, scope]),
        .ret (.ident "Effect.void")] none] := rfl

theorem inst_rawRunIn_shape {n : Nat} {τ : Subst} {x : Expr}
    (printed : inst n τ rawRunInTpl = some x) :
    ∃ receiver scope, x = .call (.ident "Effect.withFiber")
      [.arrowBlock [] [.exprStmt (.call (.ident "Fiber.runIn") [receiver, scope]),
        .ret (.ident "Effect.void")] none] := by
  aesop (add norm simp [rawRunInTpl, inst, insts, instStmts, instStmt, params,
    List.map_nil, Option.bind_eq_some_iff])

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
    by_cases special : head = "Effect.withFiber"
    · subst head
      have actual := rawRunInTpl_of_head member output hhead
      rw [actual] at printed
      obtain ⟨receiver, scope, rfl⟩ := inst_rawRunIn_shape printed
      exact eraseNode_rawRunIn n receiver scope
    · exact eraseNode_of_exprHead_except_runIn n x
        (head_of_inst n τ t x printed hhead) special
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
  {spell : String → List RowArg → Option Op} {ann : List Nat → Option (List Ty)}

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


theorem typed_action_image_normal (ann : List Nat → Option (List Ty))
    {c : EffSelfCarrier Op .action} {path : List Nat} {d : Nat} {x : Expr}
    (printed : cata_action (typedAlg sig ann) c path d = .ok x) :
    EraseTermTypes.eraseNode d x = x := by
  obtain ⟨ctor, args, hview⟩ : ∃ ctor args, view .action c = (ctor, args) := ⟨_, _, rfl⟩
  have hbuild : build .action ctor args = some c := by
    have h := build_view .action c
    rwa [hview] at h
  have hp : tableLayer.rowPrint sig .action ctor
      (atAddress path (args.map (ArgF.fold (typedAlg sig ann))) 0) d = .ok x := by
    have h := congrFun (congrFun (typed_cata_build sig ann .action ctor args c hbuild) path) d
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
    simp only [Bool.and_eq_true] at hshape
    exact eraseNode_of_table_inst hmem hout hshape.1 hinst
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
  {spell : String → List RowArg → Option Op} {ann : List Nat → Option (List Ty)}

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
            have normal := typed_action_image_normal ann hpa
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
  {spell : String → List RowArg → Option Op} {ann : List Nat → Option (List Ty)}

def TypedErasesUpTo (classes : Classes.Classes) (sig : Signature Op)
    (spell : String → List RowArg → Option Op) (ann : List Nat → Option (List Ty)) (m : Nat) : Prop :=
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
  readTyped_of_print_erasure lawful readable (eraseJoinArgs_printTypedAt lawful readable printed)

end Effect4.Codegen


namespace Effect4.Codegen.EraseTermTypes

open TypeScript Effect4.Program Effect4.Laws.Auto

variable {Op : Type}

-- Placement: exact-codecs R8; successful typed term erasure serves P3's contextual capture lift.
-- Constructor certificates form an algebra. Forgetting certificates is a homomorphism into
-- the actual typed-print algebra; final equality uses the generated hom_eq_cata laws.

def typedOriginalHom (sig : Signature Op) : TermHom TermAlgebra.id where
  f_term t := (cata_term (PrintEliminators.termAlg sig) t).1
  f_terms ts := (cata_terms (PrintEliminators.termAlg sig) ts).1
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

theorem typedTerm_original (sig : Signature Op) (t : Term) :
    (cata_term (PrintEliminators.termAlg sig) t).1 = t :=
  (hom_eq_cata_term (typedOriginalHom sig) t).trans (cata_id_term t)

theorem target_unknown : PrintEliminators.target .unknown = .ok (.name ["unknown"] []) := rfl

/-- The helper exposes a projection fact already forced by successful annotation printing.
It keeps the raw stored-fold fallback in ListFold.typeArg rather than changing its spelling. -/
theorem typeArg_of_target {ty : Ty} {target : TypeRef}
    (h : PrintEliminators.target ty = .ok target) : ListFold.typeArg ty = target := by
  unfold PrintEliminators.target at h
  cases ht : Types.ofTy ty with
  | none => rw [ht] at h; exact nomatch h
  | some value =>
    rw [ht] at h
    cases h
    simp only [ListFold.typeArg, ht, Option.getD_some]

/-- Plain atom children first erase to their ordinary argument list. The local fold inverse
then leaves the whole bare atom unchanged, using the raw non-lambda property. -/
theorem eraseTerm_plainApp (n : Nat) (name : String) (args : Terms) (values : List Expr)
    (h : values.map (eraseTerm n) = printTerms n args) :
    eraseTerm n (.call (.ident name) values) = printTerm n (.app name args) := by
  rw [eraseTerm_call, eraseTerm_ident, h]
  simpa only [eraseTerms_printTerms_identity, printTerm] using callInverse_erasedApp n name args

/-- Only the four approved cause-query heads receive unknown A and checked E at a term occurrence. -/
theorem eraseTerm_causeApp (n : Nat) (name : String) (error : TypeRef) (input : Term)
    (values : List Expr)
    (hn : ["causeIsFail", "causeIsDie", "causeIsInterrupt", "causeError"].contains name = true)
    (hv : values.map (eraseTerm n) = printTerms n (.cons input .nil)) :
    eraseTerm n (.call (.generic (.ident name) [.name ["unknown"] [], error]) values) =
      printTerm n (.app name (.cons input .nil)) := by
  have hfold : name ≠ "fold" := by
    intro h
    subst name
    exact nomatch hn
  rw [eraseTerm_call, eraseTerm_generic, eraseTerm_ident, hv]
  simp only [printTerms, callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, hfold,
    eraseCauseTermJoin, hn, ↓reduceIte, printTerm]

/-- Field R is inserted on the second curried application; literal K stays in its original place. -/
theorem eraseTerm_typedField (n : Nat) (optional : Bool) (key : String) (receiverTy : TypeRef)
    (receiver : Expr) :
    eraseTerm n (.call (.generic
      (.call (.generic (.ident (if optional then "recordOptional" else "recordRequired"))
        [.literal key]) [.str key]) [receiverTy]) [receiver]) =
      Record.writeField optional key (eraseTerm n receiver) := by
  cases optional <;>
    simp only [eraseTerm_call, eraseTerm_generic, eraseTerm_ident, eraseTerm_str,
      List.map_cons, List.map_nil, callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, ite_self,
      eraseCauseTermJoin, decide_true, ↓reduceIte, Record.writeField] <;> rfl

/-- Each checked R/V disappears at its own curried application; K stays as stored data. -/
theorem eraseTerm_typedSet (n : Nat) (key : String) (receiverTy valueTy : TypeRef)
    (receiver value : Expr) :
    eraseTerm n (.call (.generic
      (.call (.generic (.call (.generic (.ident "recordSet") [.literal key]) [.str key])
        [receiverTy]) [receiver]) [valueTy]) [value]) =
      Record.writeSet key (eraseTerm n receiver) (eraseTerm n value) := by
  have hset : ["recordRequired", "recordOptional", "recordSet"].contains "recordSet" = true := rfl
  simp only [eraseTerm_call, eraseTerm_generic, eraseTerm_ident, eraseTerm_str,
    List.map_cons, List.map_nil, callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, ite_self,
    eraseCauseTermJoin, decide_true, hset, Bool.true_and, ↓reduceIte, Record.writeSet]

/-- Inferred B/A use the bare head and two checked callback annotations. -/
theorem eraseTerm_inferredFold (n : Nat) (acc item : TypeRef) (list init body : Expr) :
    eraseTerm n (.call (.ident "fold") [list, init,
      .lambda [{ name := Template.varName n, type := some acc },
        { name := Template.varName (n + 1), type := some item }] body]) =
      ListFold.write n none (eraseTerm n list) (eraseTerm n init) (eraseTerm (n + 2) body) := by
  simp only [eraseTerm_call, eraseTerm_ident, eraseTerm_lambda,
    List.map_cons, List.map_nil, List.length_cons, List.length_nil,
    callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, eraseCauseTermJoin,
    decide_true, Bool.true_and, ↓reduceIte, ListFold.write]

/-- Stored B survives; only inferred A and the verified repetition of B disappear. -/
theorem eraseTerm_storedFold (n : Nat) (acc item : TypeRef) (list init body : Expr) :
    eraseTerm n (.call (.generic (.ident "fold") [acc, item]) [list, init,
      PrintEliminators.storedFoldStep n acc body]) =
      ListFold.write n (some acc) (eraseTerm n list) (eraseTerm n init) (eraseTerm (n + 2) body) := by
  simp only [PrintEliminators.storedFoldStep, eraseTerm_call, eraseTerm_generic,
    eraseTerm_ident, eraseTerm_lambda, List.map_cons, List.map_nil,
    List.length_cons, List.length_nil, callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin,
    eraseCauseTermJoin, decide_true, TypeRef.beq_self, Bool.true_and, ↓reduceIte, ListFold.write]

/-- A local inverse step of typed-print-erasure; term_app_certificate consumes it. -/
theorem eraseTerm_typedTuple (n : Nat) (firstTarget secondTarget : TypeRef) (first second : Expr) :
    eraseTerm n (.call (.generic (.ident "tuple") [firstTarget, secondTarget]) [first, second]) =
      .call (.ident "tuple") [eraseTerm n first, eraseTerm n second] := by
  simp only [eraseTerm_call, eraseTerm_generic, eraseTerm_ident, List.map_cons, List.map_nil,
    callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, eraseCauseTermJoin, ↓reduceIte, ite_self]

/-- A local inverse step of typed-print-erasure; the readonly slot tuple selects the checked overload. -/
theorem eraseTerm_typedPair (n : Nat) (firstTarget secondTarget : TypeRef) (first second : Expr) :
    eraseTerm n (.call (.generic (.ident "pair") [.tuple [firstTarget, secondTarget] true]) [first, second]) =
      .call (.ident "pair") [eraseTerm n first, eraseTerm n second] := by
  have notTuple : ("pair" : String) ≠ "tuple" := by decide
  simp only [eraseTerm_call, eraseTerm_generic, eraseTerm_ident, List.map_cons, List.map_nil,
    callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, eraseCauseTermJoin, notTuple, ↓reduceIte, ite_self]

theorem pure_eq_ok {α : Type} (a b : α) :
    (pure a : Except PrintRefusal α) = .ok b ↔ a = b := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    cases h
    rfl

def TermErases (v : PrintEliminators.TermCarrier .term) : Prop :=
  ∀ (env : TyEnv) (const : Bool) (x : Expr), v.2 env const = .ok x →
    eraseTerm env.length x = printTerm env.length v.1

def TermsErase (v : PrintEliminators.TermCarrier .terms) : Prop :=
  ∀ (env : TyEnv) (const : Bool) (xs : List Expr), v.2 env const = .ok xs →
    xs.map (eraseTerm env.length) = printTerms env.length v.1

theorem term_var_certificate (sig : Signature Op) (index : Var) :
    TermErases ((PrintEliminators.termAlg sig).term_var index) := by
  intro env const x hp
  simp only [PrintEliminators.termAlg, Except.ok.injEq] at hp
  subst x
  rfl

theorem term_lit_certificate (sig : Signature Op) (value : Lit) :
    TermErases ((PrintEliminators.termAlg sig).term_lit value) := by
  intro env const x hp
  simp only [PrintEliminators.termAlg, Except.ok.injEq] at hp
  subst x
  exact eraseTerm_printLit env.length value

theorem term_app_certificate (sig : Signature Op) (name : String)
    (args : PrintEliminators.TermCarrier .terms) (ha : TermsErase args) :
    TermErases ((PrintEliminators.termAlg sig).term_app name args) := by
  intro env const x hp
  simp only [PrintEliminators.termAlg] at hp
  obtain ⟨values, hvalues, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
  have hchildren := ha env (sig.constAtom name) values hvalues
  split at hp
  · rename_i hn
    cases hs : args.1 with
    | nil =>
      simp only [hs, pure_eq_ok] at hp
      subst x
      change eraseTerm env.length (.call (.ident name) values) = printTerm env.length (.app name args.1)
      exact eraseTerm_plainApp env.length name args.1 values hchildren
    | cons input rest =>
      rw [hs] at hp
      cases rest with
      | cons second tail =>
        simp only [pure_eq_ok] at hp
        subst x
        exact eraseTerm_plainApp env.length name args.1 values hchildren
      | nil =>
        obtain ⟨inputTy, hinput, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
        split at hp
        · obtain ⟨error, herror, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
          simp only [target_unknown, bind, Except.bind] at hp
          obtain ⟨errorTarget, herrorTarget, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
          simp only [withHeadTypes, Except.ok.injEq] at hp
          subst x
          change eraseTerm env.length _ = printTerm env.length (.app name args.1)
          rw [hs]
          rw [hs] at hchildren
          exact eraseTerm_causeApp env.length name errorTarget input values hn hchildren
        · simp only [pure_eq_ok] at hp
          subst x
          exact eraseTerm_plainApp env.length name args.1 values hchildren
  · split at hp
    · rename_i productName
      cases hs : args.1 with
      | nil =>
        simp only [hs, pure_eq_ok] at hp
        subst x
        exact eraseTerm_plainApp env.length name args.1 values hchildren
      | cons first rest =>
        rw [hs] at hp
        cases rest with
        | nil =>
          simp only [pure_eq_ok] at hp
          subst x
          exact eraseTerm_plainApp env.length name args.1 values hchildren
        | cons second tail =>
          cases tail with
          | cons third tail =>
            simp only [pure_eq_ok] at hp
            subst x
            exact eraseTerm_plainApp env.length name args.1 values hchildren
          | nil =>
            obtain ⟨firstTy, hfirstTy, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
            obtain ⟨secondTy, hsecondTy, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
            split at hp
            · obtain ⟨firstTarget, hfirstTarget, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
              obtain ⟨secondTarget, hsecondTarget, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
              have length : values.length = 2 := by
                have h := congrArg List.length hchildren
                simpa only [List.length_map, hs, printTerms, List.length_cons, List.length_nil] using h
              have shape : ∃ a b, values = [a, b] := by
                cases values with
                | nil => cases length
                | cons a rest =>
                  cases rest with
                  | nil => cases length
                  | cons b tail =>
                    have tailEmpty : tail = [] := by
                      cases tail with
                      | nil => rfl
                      | cons third rest =>
                        simp only [List.length_cons] at length
                        omega
                    subst tail
                    exact ⟨a, b, rfl⟩
              obtain ⟨a, b, rfl⟩ := shape
              split at hp
              · rename_i pairName
                subst name
                simp only [withHeadTypes, Except.ok.injEq] at hp
                subst x
                rw [eraseTerm_typedPair]
                change Expr.call (.ident "pair") (List.map (eraseTerm env.length) [a, b]) =
                  Expr.call (.ident "pair") (printTerms env.length args.1)
                rw [hchildren]
              · rename_i notPair
                have names : name = "pair" ∨ name = "tuple" := by
                  simpa only [List.contains_cons, List.contains_nil, Bool.or_false,
                    Bool.or_eq_true, beq_iff_eq] using productName
                have tupleName : name = "tuple" := names.resolve_left notPair
                subst name
                simp only [withHeadTypes, Except.ok.injEq] at hp
                subst x
                rw [eraseTerm_typedTuple]
                change Expr.call (.ident "tuple") (List.map (eraseTerm env.length) [a, b]) =
                  Expr.call (.ident "tuple") (printTerms env.length args.1)
                rw [hchildren]
            · simp only [pure_eq_ok] at hp
              subst x
              exact eraseTerm_plainApp env.length name args.1 values hchildren
    · simp only [pure_eq_ok] at hp
      subst x
      exact eraseTerm_plainApp env.length name args.1 values hchildren

theorem term_record_certificate (sig : Signature Op) (fields : Record.Fields) (names : List String)
    (values : PrintEliminators.TermCarrier .terms) (hv : TermsErase values) :
    TermErases ((PrintEliminators.termAlg sig).term_record fields names values) := by
  intro env const x hp
  simp only [PrintEliminators.termAlg] at hp
  obtain ⟨children, hchildren, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
  have hi := hv env true children hchildren
  cases hc : Classes.classTag? fields names values.1 with
  | none =>
    rw [hc] at hp
    simp only [pure_eq_ok] at hp
    subst x
    change eraseTerm env.length (Record.writeRecord fields names children) = printTerm env.length (.record fields names values.1)
    rw [eraseTerm_record, hi, printTerm, hc]
  | some tag =>
    rw [hc] at hp
    simp only [pure_eq_ok] at hp
    subst x
    change eraseTerm env.length (Classes.writeClass tag names.tail children.tail) = printTerm env.length (.record fields names values.1)
    simp only [eraseTerm_writeClass, List.map_tail, hi, printTerm, hc]

theorem term_field_certificate (sig : Signature Op) (mode : FieldReadMode)
    (receiver : PrintEliminators.TermCarrier .term) (key : String) (hr : TermErases receiver) :
    TermErases ((PrintEliminators.termAlg sig).term_field mode receiver key) := by
  intro env const x hp
  change eraseTerm env.length x = printTerm env.length (.field mode receiver.1 key)
  simp only [PrintEliminators.termAlg] at hp
  obtain ⟨value, hvalue, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
  have hi := hr env false value hvalue
  obtain ⟨ty, hty, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
  cases mode with
  | required =>
    simp only [Record.writeField, reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte] at hp
    split at hp
    · obtain ⟨receiverTy, hreceiverTy, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
      simp only [pure_eq_ok] at hp
      subst x
      exact (eraseTerm_typedField env.length false key receiverTy value).trans
        (congrArg (Record.writeField false key) hi)
    · simp only [pure_eq_ok] at hp
      subst x
      exact (eraseTerm_field env.length false key value).trans
        (congrArg (Record.writeField false key) hi)
  | optional =>
    simp only [Record.writeField, decide_true, ↓reduceIte] at hp
    split at hp
    · obtain ⟨receiverTy, hreceiverTy, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
      simp only [pure_eq_ok] at hp
      subst x
      exact (eraseTerm_typedField env.length true key receiverTy value).trans
        (congrArg (Record.writeField true key) hi)
    · simp only [pure_eq_ok] at hp
      subst x
      exact (eraseTerm_field env.length true key value).trans
        (congrArg (Record.writeField true key) hi)

theorem term_set_certificate (sig : Signature Op) (receiver : PrintEliminators.TermCarrier .term)
    (key : String) (replacement : PrintEliminators.TermCarrier .term)
    (hr : TermErases receiver) (hv : TermErases replacement) :
    TermErases ((PrintEliminators.termAlg sig).term_recordSet receiver key replacement) := by
  intro env const x hp
  simp only [PrintEliminators.termAlg] at hp
  obtain ⟨value, hvalue, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
  obtain ⟨newValue, hnewValue, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
  have hiReceiver := hr env false value hvalue
  have hiValue := hv env true newValue hnewValue
  obtain ⟨receiverTy, hreceiverTy, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
  obtain ⟨valueTy, hvalueTy, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
  split at hp
  · obtain ⟨receiverTarget, hreceiverTarget, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
    obtain ⟨valueTarget, hvalueTarget, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
    simp only [pure_eq_ok] at hp
    subst x
    rw [eraseTerm_typedSet, hiReceiver, hiValue]
    rfl
  · simp only [pure_eq_ok] at hp
    subst x
    rw [eraseTerm_set, hiReceiver, hiValue]
    rfl

theorem term_tuple_certificate (sig : Signature Op) (receiver : PrintEliminators.TermCarrier .term)
    (index : Nat) (hr : TermErases receiver) :
    TermErases ((PrintEliminators.termAlg sig).term_tupleAt receiver index) := by
  intro env const x hp
  simp only [PrintEliminators.termAlg] at hp
  obtain ⟨value, hvalue, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
  simp only [pure_eq_ok] at hp
  subst x
  rw [eraseTerm_tupleAt, hr env false value hvalue]
  rfl

theorem term_fold_certificate (sig : Signature Op) (stored : Option Ty)
    (list init body : PrintEliminators.TermCarrier .term)
    (hl : TermErases list) (hi : TermErases init) (hb : TermErases body) :
    TermErases ((PrintEliminators.termAlg sig).term_fold stored list init body) := by
  intro env const x hp
  simp only [PrintEliminators.termAlg] at hp
  obtain ⟨listTy, hlistTy, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
  obtain ⟨item, hitem, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
  obtain ⟨initTy, hinitTy, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
  obtain ⟨listExpr, hlistExpr, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
  obtain ⟨initExpr, hinitExpr, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
  obtain ⟨bodyExpr, hbodyExpr, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
  have hiList := hl env false listExpr hlistExpr
  have hiInit := hi env false initExpr hinitExpr
  have hiBody := hb (env ++ [stored.getD initTy, item]) false bodyExpr hbodyExpr
  simp only [List.length_append, List.length_cons, List.length_nil] at hiBody
  split at hp
  · obtain ⟨accTarget, haccTarget, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
    obtain ⟨itemTarget, hitemTarget, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
    cases stored with
    | none =>
      simp only [pure_eq_ok] at hp
      subst x
      rw [eraseTerm_inferredFold, hiList, hiInit, hiBody]
      rfl
    | some acc =>
      simp only [pure_eq_ok] at hp
      subst x
      have hstored : ListFold.typeArg acc = accTarget := typeArg_of_target haccTarget
      rw [eraseTerm_storedFold, hiList, hiInit, hiBody]
      simp only [PrintEliminators.termAlg, printTerm, Option.map_some, hstored]
  · simp only [pure_eq_ok] at hp
    subst x
    rw [eraseTerm_rawFold, hiList, hiInit, hiBody]
    rfl

theorem terms_nil_certificate (sig : Signature Op) :
    TermsErase (PrintEliminators.termAlg sig).terms_nil := by
  intro env const xs hp
  simp only [PrintEliminators.termAlg, Except.ok.injEq] at hp
  subst xs
  rfl

theorem terms_cons_certificate (sig : Signature Op) (first : PrintEliminators.TermCarrier .term)
    (rest : PrintEliminators.TermCarrier .terms) (hf : TermErases first) (hr : TermsErase rest) :
    TermsErase ((PrintEliminators.termAlg sig).terms_cons first rest) := by
  intro env const xs hp
  simp only [PrintEliminators.termAlg] at hp
  obtain ⟨value, hvalue, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
  obtain ⟨tail, htail, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
  simp only [pure_eq_ok] at hp
  subst xs
  simp only [List.map_cons, PrintEliminators.termAlg, printTerms]
  rw [hf env const value hvalue, hr env const tail htail]

def TypedCertificateCarrier : TermFam → Type
  | .term => { v : PrintEliminators.TermCarrier .term // TermErases v }
  | .terms => { v : PrintEliminators.TermCarrier .terms // TermsErase v }

def typedCertificateAlg (sig : Signature Op) : TermAlgebra TypedCertificateCarrier where
  term_var index := ⟨(PrintEliminators.termAlg sig).term_var index, term_var_certificate sig index⟩
  term_lit value := ⟨(PrintEliminators.termAlg sig).term_lit value, term_lit_certificate sig value⟩
  term_app name args := ⟨(PrintEliminators.termAlg sig).term_app name args.val, term_app_certificate sig name args.val args.property⟩
  term_record fields names values := ⟨(PrintEliminators.termAlg sig).term_record fields names values.val,
    term_record_certificate sig fields names values.val values.property⟩
  term_field mode receiver key := ⟨(PrintEliminators.termAlg sig).term_field mode receiver.val key,
    term_field_certificate sig mode receiver.val key receiver.property⟩
  term_recordSet receiver key value := ⟨(PrintEliminators.termAlg sig).term_recordSet receiver.val key value.val,
    term_set_certificate sig receiver.val key value.val receiver.property value.property⟩
  term_tupleAt receiver index := ⟨(PrintEliminators.termAlg sig).term_tupleAt receiver.val index,
    term_tuple_certificate sig receiver.val index receiver.property⟩
  term_fold stored list init body := ⟨(PrintEliminators.termAlg sig).term_fold stored list.val init.val body.val,
    term_fold_certificate sig stored list.val init.val body.val list.property init.property body.property⟩
  terms_nil := ⟨(PrintEliminators.termAlg sig).terms_nil, terms_nil_certificate sig⟩
  terms_cons first rest := ⟨(PrintEliminators.termAlg sig).terms_cons first.val rest.val,
    terms_cons_certificate sig first.val rest.val first.property rest.property⟩

/-- Forgetting the erasure certificates gives the actual typed printer, field by field. -/
def typedCertificateHom (sig : Signature Op) : TermHom (PrintEliminators.termAlg sig) where
  f_term t := (cata_term (typedCertificateAlg sig) t).val
  f_terms ts := (cata_terms (typedCertificateAlg sig) ts).val
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

/-- Successful typed term printing erases to ordinary printing, by the generated fold agreement.
It assumes no readable, unannotated, formed-type, or extra projection premise. -/
theorem eraseTerm_printTerm (sig : Signature Op) (t : Term) (env : TyEnv) (const : Bool)
    {x : Expr} (hp : PrintEliminators.term sig env const t = .ok x) :
    eraseTerm env.length x = printTerm env.length t := by
  have h := (cata_term (typedCertificateAlg sig) t).property env const x
  have folded := hom_eq_cata_term (typedCertificateHom sig) t
  change (cata_term (typedCertificateAlg sig) t).val = cata_term (PrintEliminators.termAlg sig) t at folded
  rw [folded] at h
  have result := h hp
  rw [typedTerm_original] at result
  exact result

end Effect4.Codegen.EraseTermTypes

namespace Effect4.Codegen.EraseTermTypes

open TypeScript Effect4.Program Effect4.Laws.Auto

variable {Op : Type}

-- Placement: exact-codecs R8; cause certificates serve P3's cause capture erasure bridge.
def CauseErases (v : CauseTerm × (TyEnv → Except PrintRefusal Expr)) : Prop :=
  ∀ (env : TyEnv) (x : Expr), v.2 env = .ok x → eraseCause env.length x = printCause env.length v.1

def TypedCauseCarrier (_ : CauseTermFam) : Type :=
  { v : CauseTerm × (TyEnv → Except PrintRefusal Expr) // CauseErases v }

theorem cause_fail_certificate (sig : Signature Op) (t : Term) :
    CauseErases (.fail t, (PrintEliminators.causeAlg sig).cause_fail t) := by
  intro env x hp
  simp only [PrintEliminators.causeAlg] at hp
  obtain ⟨value, hvalue, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
  simp only [pure_eq_ok] at hp
  subst x
  simp only [eraseCause, eraseTerm_call, eraseTerm_ident, List.map_cons, List.map_nil,
    eraseTerm_printTerm sig t env false hvalue]
  simp only [callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, ite_self, eraseCauseTermJoin, printCause]

theorem cause_die_certificate (sig : Signature Op) (t : Term) :
    CauseErases (.die t, (PrintEliminators.causeAlg sig).cause_die t) := by
  intro env x hp
  simp only [PrintEliminators.causeAlg] at hp
  obtain ⟨value, hvalue, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
  simp only [pure_eq_ok] at hp
  subst x
  simp only [eraseCause, eraseTerm_call, eraseTerm_ident, List.map_cons, List.map_nil,
    eraseTerm_printTerm sig t env false hvalue]
  simp only [callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, ite_self, eraseCauseTermJoin, printCause]

theorem cause_interrupt_certificate (sig : Signature Op) (who : Option Term) :
    CauseErases (.interrupt who, (PrintEliminators.causeAlg sig).cause_interrupt who) := by
  intro env x hp
  cases who with
  | none =>
    change (.ok (.call (.ident "Cause.interrupt") []) : Except PrintRefusal Expr) = .ok x at hp
    cases hp
    simp only [eraseCause, eraseTerm_call, eraseTerm_ident, List.map_nil,
      callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, ite_self, eraseCauseTermJoin, printCause]
  | some t =>
    simp only [PrintEliminators.causeAlg, Option.toList_some,
      List.mapM_cons, List.mapM_nil] at hp
    obtain ⟨values, hvalues, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
    obtain ⟨value, hvalue, hvalues⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hvalues
    change (.ok [value] : Except PrintRefusal (List Expr)) = .ok values at hvalues
    cases hvalues
    simp only [pure_eq_ok] at hp
    subst x
    simp only [eraseCause, eraseTerm_call, eraseTerm_ident, List.map_cons, List.map_nil,
      eraseTerm_printTerm sig t env false hvalue]
    simp only [callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, ite_self, eraseCauseTermJoin, printCause]

theorem cause_both_certificate (sig : Signature Op) (left right : TypedCauseCarrier .cause) :
    CauseErases (.both left.val.1 right.val.1,
      (PrintEliminators.causeAlg sig).cause_both left.val.2 right.val.2) := by
  intro env x hp
  simp only [PrintEliminators.causeAlg] at hp
  obtain ⟨leftExpr, hleft, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
  obtain ⟨rightExpr, hright, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
  simp only [pure_eq_ok] at hp
  subst x
  have hl := left.property env leftExpr hleft
  have hr := right.property env rightExpr hright
  simp only [eraseCause] at hl hr ⊢
  simp only [eraseTerm_call, eraseTerm_ident, List.map_cons, List.map_nil, hl, hr]
  simp only [callInverse, eraseProductJoin, eraseRecordJoin, eraseFoldJoin, ite_self, eraseCauseTermJoin, printCause]

def typedCauseCertificateAlg (sig : Signature Op) : CauseTermAlgebra TypedCauseCarrier where
  cause_fail t := ⟨(.fail t, (PrintEliminators.causeAlg sig).cause_fail t), cause_fail_certificate sig t⟩
  cause_die t := ⟨(.die t, (PrintEliminators.causeAlg sig).cause_die t), cause_die_certificate sig t⟩
  cause_interrupt who := ⟨(.interrupt who, (PrintEliminators.causeAlg sig).cause_interrupt who),
    cause_interrupt_certificate sig who⟩
  cause_both left right := ⟨(.both left.val.1 right.val.1,
    (PrintEliminators.causeAlg sig).cause_both left.val.2 right.val.2), cause_both_certificate sig left right⟩

def typedCauseCertificateHom (sig : Signature Op) : CauseTermHom (PrintEliminators.causeAlg sig) where
  f_cause c := (cata_cause (typedCauseCertificateAlg sig) c).val.2
  h_cause_fail _ := rfl
  h_cause_die _ := rfl
  h_cause_interrupt _ := rfl
  h_cause_both _ _ := rfl

def typedCauseOriginalHom (sig : Signature Op) : CauseTermHom CauseTermAlgebra.id where
  f_cause c := (cata_cause (typedCauseCertificateAlg sig) c).val.1
  h_cause_fail _ := rfl
  h_cause_die _ := rfl
  h_cause_interrupt _ := rfl
  h_cause_both _ _ := rfl

/-- Successful typed cause printing erases to the ordinary cause print by generated fold agreement. -/
theorem eraseCause_typedCause (sig : Signature Op) (env : TyEnv) (c : CauseTerm) {x : Expr}
    (hp : cata_cause (PrintEliminators.causeAlg sig) c env = .ok x) :
    eraseCause env.length x = printCause env.length c := by
  have h := (cata_cause (typedCauseCertificateAlg sig) c).property env x
  have folded := hom_eq_cata_cause (typedCauseCertificateHom sig) c
  change (cata_cause (typedCauseCertificateAlg sig) c).val.2 = cata_cause (PrintEliminators.causeAlg sig) c at folded
  rw [folded] at h
  have result := h hp
  have original : (cata_cause (typedCauseCertificateAlg sig) c).val.1 = c :=
    (hom_eq_cata_cause (typedCauseOriginalHom sig) c).trans (cata_id_cause c)
  rw [original] at result
  exact result

end Effect4.Codegen.EraseTermTypes

/-!
Actual source addresses supply the context of typed-site erasure.
Placement: exact-codecs, R8; helper of successful Program.printTyped erasure.
Consumer: the generalized source-image induction at recursive template captures.
The helpers identify existing Node data; they store no second program representation.
-/
set_option autoImplicit false
namespace Effect4.Codegen
open Effect4.Program Template Templates
variable {Op : Type}

def nodeOfFamily : (fam : EffFam) → EffSelfCarrier Op fam → Node Op
  | .eff, source => .eff source
  | .action, source => .action source
  | .layer, source => .layer source
  | .stmt, source => .stmt source
  | .stmts, source => .stmts source
  | .effs, source => .effs source
  | .layers, source => .layers source

def sourceChild : ArgF Op (EffSelfCarrier Op) → Option (Node Op)
  | .child fam source => some (nodeOfFamily fam source)
  | _ => none

theorem child_of_view (fam : EffFam) (source : EffSelfCarrier Op fam) (i : Nat) :
    (nodeOfFamily fam source).child i = ((view fam source).2.filterMap sourceChild)[i]? := by
  cases fam <;> cases source <;> cases i with
  | zero => rfl
  | succ i =>
    cases i with
    | zero => rfl
    | succ i =>
      cases i with
      | zero => rfl
      | succ i => rfl

theorem sourceChild_at_count :
    ∀ (args : List (ArgF Op (EffSelfCarrier Op))) (i : Nat) (fam : EffFam)
      (source : EffSelfCarrier Op fam), args[i]? = some (.child fam source) →
    (args.filterMap sourceChild)[(args.take i).countP isChildArg]? = some (nodeOfFamily fam source)
  | [], _, _, _, member => by cases member
  | arg :: args, 0, fam, source, member => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at member
    subst arg
    rfl
  | arg :: args, i + 1, fam, source, member => by
    have smaller := sourceChild_at_count args i fam source
      (by simpa only [List.getElem?_cons_succ] using member)
    cases arg with
    | child childFam child =>
      simpa only [List.filterMap_cons, sourceChild, List.take_succ_cons, List.countP_cons,
        isChildArg, argSortOf, ↓reduceIte, List.getElem?_cons_succ] using smaller
    | _ =>
      simpa only [List.filterMap_cons, sourceChild, List.take_succ_cons, List.countP_cons,
        isChildArg, argSortOf, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using smaller

theorem source_child_of_view {fam : EffFam} {source : EffSelfCarrier Op fam}
    {ctor : String} {args : List (ArgF Op (EffSelfCarrier Op))}
    (viewed : view fam source = (ctor, args)) {i : Nat} {childFam : EffFam}
    {child : EffSelfCarrier Op childFam} (member : args[i]? = some (.child childFam child)) :
    (nodeOfFamily fam source).child ((args.take i).countP isChildArg) =
      some (nodeOfFamily childFam child) := by
  rw [child_of_view, viewed]
  exact sourceChild_at_count args i childFam child member

end Effect4.Codegen


set_option autoImplicit false

namespace Effect4.Codegen.PrintEliminators

open Effect4.Program

variable {Op : Type}

-- Placement: exact-codecs R8, typed-print erasure's actual-context step.
-- Consumer: the typed site algebra's context invariant at each source address.
theorem contextAtTable_annotate_facts
    {s : Signature Op} {env0 : TyEnv} {p : Eff Op} {path : List Nat}
    {ctx : Context Op}
    (found : contextAtTable (annotate s env0 p) p path = some ctx) :
    (Node.eff p).at_ path = some ctx.node ∧
    ∃ rho : NodeEnv,
      (Node.eff p).envAt s (.env env0) path = some rho ∧
      ctx.env = rho.tyEnv ∧ ctx.path = path ∧
      ctx.entries = some (annotate s env0 p) := by
  unfold contextAtTable at found
  obtain ⟨node, hnode, found⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨entry, hentry, found⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨rho, henv, assembled⟩ := Option.bind_eq_some_iff.mp found
  have hctx := Option.some.inj assembled
  cases hctx
  refine ⟨hnode, ?_⟩
  have member := List.mem_of_find?_eq_some hentry
  have samePath := List.find?_some hentry
  rw [annotate_eq_table] at member
  simp only [table, List.mem_map] at member
  obtain ⟨a, -, rfl⟩ := member
  change decide (a = path) = true at samePath
  have ha : a = path := of_decide_eq_true samePath
  subst a
  exact ⟨rho, henv, rfl, rfl, rfl⟩

end Effect4.Codegen.PrintEliminators


/-!
The checked source context indexes the full typed-site print relation.
Placement: exact-codecs R8; consumer: successful Program.printTyped erasure and existing read laws.
The source/environment premises are discharged at the root and transported along existing child paths.
No whole-program typing certificate or desired erasure equation is a premise.
-/
set_option autoImplicit false
namespace Effect4.Codegen
open TypeScript Effect4.Program Template Templates
variable {Op : Type}

def PrintedCaptureAt (alg : EffAlgebra Op TCarrier) (path : List Nat) (n : Nat) :
    (fam : EffFam) → EffSelfCarrier Op fam → Arg → Prop
  | .eff, source, .expr x => cata_eff alg source path n = .ok x
  | .action, source, .expr x => cata_action alg source path n = .ok x
  | .layer, source, .expr x => cata_layer alg source path n = .ok x
  | .effs, source, .exprs xs => cata_effs alg source path n = .ok xs
  | .layers, source, .exprs xs => cata_layers alg source path n = .ok xs
  | .stmts, source, .stmts ss => cata_stmts alg source path n = .ok ss
  | _, _, _ => False

theorem printedCaptureAt_of_printArg {sig : Signature Op} {alg : EffAlgebra Op TCarrier}
    {path : List Nat} {depth : Nat} {fam : EffFam} {source : EffSelfCarrier Op fam} {capture : Arg}
    (printed : Templates.printArg sig depth (.child fam (cataFam alg fam source path)) =
      .ok (some capture)) : PrintedCaptureAt alg path depth fam source capture := by
  cases fam <;> cases capture <;>
    aesop (add norm simp [PrintedCaptureAt, cataFam, Templates.printArg, bind, Except.bind,
      pure, Except.pure])

theorem atAddress_fold_child_for (alg : EffAlgebra Op TCarrier)
    (path : List Nat) (args : List (ArgF Op (EffSelfCarrier Op))) (i : Nat)
    (fam : EffFam) (source : EffSelfCarrier Op fam)
    (member : args[i]? = some (.child fam source)) :
    (atAddress path (args.map (ArgF.fold alg)) 0)[i]? =
      some (.child fam (cataFam alg fam source (path ++ [(args.take i).countP isChildArg]))) := by
  have folded : (args.map (ArgF.fold alg))[i]? = some (.child fam (cataFam alg fam source)) := by
    simp only [List.getElem?_map, member, Option.map_some, ArgF.fold]
  rw [atAddress_getElem_child path _ 0 i fam _ folded, countChildArgs_fold, Nat.zero_add]

theorem atAddress_fold_leaf_for (alg : EffAlgebra Op TCarrier) (sig : Signature Op)
    (path : List Nat) (args : List (ArgF Op (EffSelfCarrier Op))) (i : Nat)
    (source : ArgF Op (EffSelfCarrier Op))
    (leaf : ∀ fam child, source ≠ .child fam child) (member : args[i]? = some source) :
    (atAddress path (args.map (ArgF.fold alg)) 0)[i]? = some (ArgF.fold (printAlg sig) source) := by
  rw [atAddress_getElem, List.getElem?_map, member, Option.map_some, Option.bind_some]
  cases source with
  | child fam child => exact False.elim (leaf fam child rfl)
  | _ => rfl

def ClosedSiteLevel (fam : EffFam) (n : Nat) : Prop :=
  match fam with
  | .layer | .layers => n = 0
  | _ => True

def SiteFocused (root : Eff Op) (sig : Signature Op) (env0 : TyEnv)
    (path : List Nat) (fam : EffFam) (source : EffSelfCarrier Op fam) (n : Nat) : Prop :=
  (Node.eff root).at_ path = some (nodeOfFamily fam source) ∧
    ∃ rho, (Node.eff root).envAt sig (.env env0) path = some rho ∧
      rho.tyEnv.length = n ∧ ClosedSiteLevel fam n

theorem siteFocused_root (root : Eff Op) (sig : Signature Op) (env0 : TyEnv) :
    SiteFocused root sig env0 [] .eff root env0.length := ⟨rfl, .env env0, rfl, rfl, True.intro⟩

theorem site_context_matches {sig : Signature Op} {root : Eff Op} {env0 : TyEnv}
    {path : List Nat} {fam : EffFam} {source : EffSelfCarrier Op fam} {n : Nat}
    {ctx : PrintEliminators.Context Op}
    (focus : SiteFocused root sig env0 path fam source n)
    (found : PrintEliminators.contextAtTable (annotate sig env0 root) root path = some ctx) :
    ctx.node = nodeOfFamily fam source ∧ ctx.env.length = n := by
  obtain ⟨node, rho, environment, henv, _, _⟩ :=
    PrintEliminators.contextAtTable_annotate_facts found
  obtain ⟨sourceAt, rho', environment', length, _⟩ := focus
  have sameNode := Option.some.inj (node.symm.trans sourceAt)
  have sameEnv := Option.some.inj (environment.symm.trans environment')
  subst rho'
  exact ⟨sameNode, by rw [henv]; exact length⟩

def SitesEraseUpTo (classes : Classes.Classes) (sig : Signature Op)
    (spell : String → List RowArg → Option Op) (root : Eff Op) (env0 : TyEnv)
    (ann : List Nat → Option (List Ty)) (m : Nat) : Prop :=
  let alg := typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root)
  (∀ fam path n (source : EffSelfCarrier Op fam) (x : Expr), sizeOf x ≤ m →
    SiteFocused root sig env0 path fam source n → ReadableAt classes sig fam source n →
    PrintedCaptureAt alg path n fam source (.expr x) →
    (∃ plain, eraseT classes sig spell fam n x = some plain ∧ PrintsTo sig n fam source (.expr plain)) ∧
      nodeLike (EraseTermTypes.eraseNode n x) = true) ∧
  (∀ fam path n (source : EffSelfCarrier Op fam) (xs : List Expr), sizeOf xs ≤ m →
    SiteFocused root sig env0 path fam source n → ReadableAt classes sig fam source n →
    PrintedCaptureAt alg path n fam source (.exprs xs) →
    PrintsTo sig n fam source (.exprs (eraseSpine classes sig spell fam n xs))) ∧
  (∀ path n (source : Stmts Op) (ss : List TypeScript.Stmt), sizeOf ss ≤ m →
    SiteFocused root sig env0 path .stmts source n → ReadableAt classes sig .stmts source n →
    PrintedCaptureAt alg path n .stmts source (.stmts ss) →
    PrintsTo sig n .stmts source (.stmts (eraseStmts classes sig spell n ss)))

end Effect4.Codegen


namespace Effect4.Codegen.PrintEliminators

open Effect4.Program TypeScript

variable {Op : Type}

-- Placement: exact-codecs R8, step of typed-print erasure.
-- Consumer: contextual template capture agreement for a successful typed term slot.
-- The existing success guard supplies the exact template depth; no new typing premise.
theorem printArg_term_erases (sig : Signature Op) (ctx : Context Op)
    (index depth : Nat) (t : Term) {value : Expr}
    (printed : printArg sig ctx index depth (.term t) = .ok (some (.expr value))) :
    EraseTermTypes.eraseTerm depth value = printTerm depth t := by
  cases henv : slotEnv sig ctx index with
  | none =>
    simp only [printArg, henv, need, bind, Except.bind] at printed
    cases printed
  | some env =>
    simp only [printArg, henv, need, bind, Except.bind] at printed
    split at printed
    · rename_i depthMatches
      obtain ⟨x, hx, assembled⟩ := Effect4.Laws.Auto.bind_eq_ok.mp printed
      simp only [EraseTermTypes.pure_eq_ok, Option.some.injEq, Template.Arg.expr.injEq] at assembled
      subst value
      simpa only [depthMatches] using EraseTermTypes.eraseTerm_printTerm sig t env false hx
    · cases printed

-- Same capture law at the optional term sort; absence remains the old template behavior.
theorem printArg_optTerm_erases (sig : Signature Op) (ctx : Context Op)
    (index depth : Nat) (t : Term) {value : Expr}
    (printed : printArg sig ctx index depth (.optTerm (some t)) = .ok (some (.expr value))) :
    EraseTermTypes.eraseTerm depth value = printTerm depth t := by
  cases henv : slotEnv sig ctx index with
  | none =>
    simp only [printArg, henv, need, bind, Except.bind] at printed
    cases printed
  | some env =>
    simp only [printArg, henv, need, bind, Except.bind] at printed
    split at printed
    · rename_i depthMatches
      obtain ⟨x, hx, assembled⟩ := Effect4.Laws.Auto.bind_eq_ok.mp printed
      simp only [EraseTermTypes.pure_eq_ok, Option.some.injEq, Template.Arg.expr.injEq] at assembled
      subst value
      simpa only [depthMatches] using EraseTermTypes.eraseTerm_printTerm sig t env false hx
    · cases printed

-- Cause captures use the checked cause fold at the same explicitly guarded depth.
theorem printArg_cause_erases (sig : Signature Op) (ctx : Context Op)
    (index depth : Nat) (c : CauseTerm) {value : Expr}
    (printed : printArg sig ctx index depth (.cause c) = .ok (some (.expr value))) :
    EraseTermTypes.eraseCause depth value = printCause depth c := by
  simp only [printArg] at printed
  split at printed
  · rename_i depthMatches
    obtain ⟨x, hx, assembled⟩ := Effect4.Laws.Auto.bind_eq_ok.mp printed
    simp only [EraseTermTypes.pure_eq_ok, Option.some.injEq, Template.Arg.expr.injEq] at assembled
    subst value
    simpa only [depthMatches] using EraseTermTypes.eraseCause_typedCause sig ctx.env c hx
  · cases printed

end Effect4.Codegen.PrintEliminators


/-!
Successful typed scalar captures erase at the actual template depth.
Placement: exact-codecs R8; consumer: generalized source capture agreement.
Successful leaf printing supplies its slot-depth guard; no typing certificate is added.
-/
set_option autoImplicit false
namespace Effect4.Codegen
open TypeScript Effect4.Program Template Templates
variable {Op : Type}

theorem site_term_capture_shape (sig : Signature Op) (ctx : PrintEliminators.Context Op)
    (index depth : Nat) (source : Term) {capture : Arg}
    (printed : PrintEliminators.printArg sig ctx index depth (.term source) = .ok (some capture)) :
    ∃ value, capture = .expr value := by
  cases envAt : PrintEliminators.slotEnv sig ctx index with
  | none =>
    simp only [PrintEliminators.printArg, envAt, PrintEliminators.need, bind, Except.bind] at printed
    cases printed
  | some env =>
    simp only [PrintEliminators.printArg, envAt, PrintEliminators.need, bind, Except.bind] at printed
    split at printed
    · obtain ⟨value, _, assembled⟩ := bind_eq_ok.mp printed
      cases assembled
      exact ⟨value, rfl⟩
    · cases printed

theorem site_optTerm_capture_shape (sig : Signature Op) (ctx : PrintEliminators.Context Op)
    (index depth : Nat) (source : Term) {capture : Arg}
    (printed : PrintEliminators.printArg sig ctx index depth (.optTerm (some source)) = .ok (some capture)) :
    ∃ value, capture = .expr value := by
  cases envAt : PrintEliminators.slotEnv sig ctx index with
  | none =>
    simp only [PrintEliminators.printArg, envAt, PrintEliminators.need, bind, Except.bind] at printed
    cases printed
  | some env =>
    simp only [PrintEliminators.printArg, envAt, PrintEliminators.need, bind, Except.bind] at printed
    split at printed
    · obtain ⟨value, _, assembled⟩ := bind_eq_ok.mp printed
      cases assembled
      exact ⟨value, rfl⟩
    · cases printed

theorem site_cause_capture_shape (sig : Signature Op) (ctx : PrintEliminators.Context Op)
    (index depth : Nat) (source : CauseTerm) {capture : Arg}
    (printed : PrintEliminators.printArg sig ctx index depth (.cause source) = .ok (some capture)) :
    ∃ value, capture = .expr value := by
  simp only [PrintEliminators.printArg] at printed
  split at printed
  · obtain ⟨value, _, assembled⟩ := bind_eq_ok.mp printed
    cases assembled
    exact ⟨value, rfl⟩
  · cases printed

theorem siteScalar_printArg (sig : Signature Op) (ctx : PrintEliminators.Context Op)
    (row : Templates.Row) (sorts : List ArgSort) (n : Nat) (σ : Subst)
    (child : EffFam → Nat → (y : Expr) → (i : Nat) → (i, .expr y) ∈ σ → Expr)
    (children : EffFam → Nat → (ys : List Expr) → (i : Nat) → (i, .exprs ys) ∈ σ → List Expr)
    (block : Nat → (ss : List TypeScript.Stmt) → (i : Nat) → (i, .stmts ss) ∈ σ → List TypeScript.Stmt)
    (i : Nat) (source : ArgF Op (EffSelfCarrier Op))
    (leaf : ∀ fam value, source ≠ .child fam value)
    (sort : sorts[i]? = some (argSortOf source))
    (capture : Arg) (member : (i, capture) ∈ σ)
    (printed : PrintEliminators.printArg sig ctx i
      (argDepth row.fam (argSortOf source) n (row.out.levelAt i)) (ArgF.fold (printAlg sig) source) =
        .ok (some capture)) :
    Templates.printArg sig (argDepth row.fam (argSortOf source) n (row.out.levelAt i))
      (ArgF.fold (printAlg sig) source) =
      .ok (some (eraseCapture row sorts n σ child children block ⟨(i, capture), member⟩)) := by
  cases source with
  | child fam source => exact False.elim (leaf fam source rfl)
  | term source =>
    obtain ⟨value, rfl⟩ := site_term_capture_shape sig ctx i _ source printed
    have erased := PrintEliminators.printArg_term_erases sig ctx i _ source printed
    simp only [argSortOf] at erased
    simp only [Templates.printArg, ArgF.fold, eraseCapture, sort, argSortOf,
      Option.getD_some, erased]
  | cause source =>
    obtain ⟨value, rfl⟩ := site_cause_capture_shape sig ctx i _ source printed
    have erased := PrintEliminators.printArg_cause_erases sig ctx i _ source printed
    simp only [argSortOf] at erased
    simp only [Templates.printArg, ArgF.fold, eraseCapture, sort, argSortOf,
      Option.getD_some, erased]
  | optTerm source =>
    cases source with
    | none => cases printed
    | some source =>
      obtain ⟨value, rfl⟩ := site_optTerm_capture_shape sig ctx i _ source printed
      have erased := PrintEliminators.printArg_optTerm_erases sig ctx i _ source printed
      simp only [argSortOf] at erased
      simp only [Templates.printArg, ArgF.fold, eraseCapture, sort, argSortOf,
        Option.getD_some, erased]
  | _ =>
    have ordinary := printed
    simp only [PrintEliminators.printArg, ArgF.fold] at ordinary
    rw [eraseCapture_printLeaf sig row sorts n σ child children block i _
      (fun fam source eq => by cases eq) sort capture member ordinary]
    exact ordinary

end Effect4.Codegen


/-! Actual typed-site argument lookup, exact-codecs R8.
Consumer: generalized source capture agreement for successful Program.printTyped erasure. -/
set_option autoImplicit false
namespace Effect4.Codegen.PrintEliminators
open TypeScript Effect4.Program Template Templates
variable {Op : Type}
theorem printArgs_lookup {sig : Signature Op} (ctx : Context Op) {fam : EffFam} {n : Nat} {out : RowOut} :
    ∀ (as : List (ArgF Op Carrier)) (i : Nat) (τ : Subst), printArgs sig ctx fam n out as i = .ok τ →
    (∀ (k : Nat) (a : ArgF Op Carrier), as[k]? = some a →
      printArg sig ctx (i + k) (argDepth fam (argSortOf a) n (out.levelAt (i + k))) a = .ok (lookup τ (i + k))) ∧
    (∀ j, j < i → lookup τ j = none)
  | [], _, _, _ => by aesop (add norm simp [printArgs, lookup])
  | b :: bs, i, τ, h => by
    simp only [printArgs, bind_eq_ok] at h
    obtain ⟨x, hx, rest, hrest, hτ⟩ := h
    obtain ⟨ih, ihlow⟩ := printArgs_lookup ctx (sig := sig) (fam := fam) (n := n) (out := out)
      bs (i + 1) rest hrest
    cases x with
    | none =>
      cases hτ
      refine ⟨fun k a hk => ?_, fun j hj => ihlow j (by omega)⟩
      cases k with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hk; subst hk
                simpa only [Nat.add_zero, ihlow i (by omega)] using hx
      | succ k => rw [show i + (k + 1) = i + 1 + k by omega]; exact ih k a hk
    | some v =>
      cases hτ
      have hup : ∀ k, lookup ((i, v) :: rest) (i + (k + 1)) = lookup rest (i + (k + 1)) :=
        fun k => lookup_cons_ne i _ v rest (by omega)
      have hlow : ∀ j, j < i → lookup ((i, v) :: rest) j = lookup rest j :=
        fun j hj => lookup_cons_ne i j v rest (by omega)
      refine ⟨fun k a hk => ?_, fun j hj => by rw [hlow j hj]; exact ihlow j (by omega)⟩
      cases k with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hk; subst hk
                simpa only [Nat.add_zero, lookup_cons_self] using hx
      | succ k => rw [hup k, show i + (k + 1) = i + 1 + k by omega]; exact ih k a hk


end Effect4.Codegen.PrintEliminators


/-!
Proposed helper of typed-print erasure: exact-codecs, R8.
A matched capture must identify an actual source argument.
The printArgs erasure bridge consumes this inverse of the existing lookup law.
This is a scratch candidate until the serial lease holder checks it.
-/

set_option autoImplicit false

namespace Effect4.Codegen.PrintEliminators

open Effect4.Program Effect4.Codegen.Template Effect4.Codegen.Templates

variable {Op : Type}

/-- A captured argument comes from its source position, at the row's actual binder depth.
The consumer is the printArgs erasure bridge of typed-print erasure (exact-codecs, R8). -/
theorem printArgs_lookup_some {sig : Signature Op} (ctx : Context Op) {fam : EffFam} {n : Nat} {out : RowOut} :
    ∀ (args : List (ArgF Op Carrier)) (i : Nat) (τ : Subst),
      printArgs sig ctx fam n out args i = .ok τ →
      ∀ (j : Nat) (capture : Arg), lookup τ j = some capture →
      ∃ (k : Nat) (arg : ArgF Op Carrier), j = i + k ∧ args[k]? = some arg ∧
        printArg sig ctx j (argDepth fam (argSortOf arg) n (out.levelAt j)) arg = .ok (some capture)
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
        printArgs_lookup_some ctx args (i + 1) _ tail j capture found
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
          printArgs_lookup_some ctx args (i + 1) rest tail j capture found
        exact ⟨k + 1, item, by omega, member, printed⟩

end Effect4.Codegen.PrintEliminators


/-!
Actual source slots supply local scalar and recursive-child erasure certificates.
Placement: exact-codecs R8; consumer: eraseCaptures_siteArgs at expression and statement rows.
Recursive certificates are the smaller-target induction hypotheses at exact source addresses.
-/
set_option autoImplicit false
namespace Effect4.Codegen
open TypeScript Effect4.Program Template Templates
variable {Op : Type}

set_option maxHeartbeats 2000000 in
theorem source_site_slot_transport (classes : Classes.Classes) (sig : Signature Op)
    (alg : EffAlgebra Op TCarrier) (path : List Nat) (ctx : PrintEliminators.Context Op)
    (row : Templates.Row) (n : Nat) (args : List (ArgF Op (EffSelfCarrier Op))) (σ : Subst)
    (child : EffFam → Nat → (y : Expr) → (i : Nat) → (i, .expr y) ∈ σ → Expr)
    (children : EffFam → Nat → (ys : List Expr) → (i : Nat) → (i, .exprs ys) ∈ σ → List Expr)
    (block : Nat → (ss : List TypeScript.Stmt) → (i : Nat) → (i, .stmts ss) ∈ σ → List TypeScript.Stmt)
    (readable : argsReadable classes sig row.fam n row.out (rowDaemon row)
      (args.map (ArgF.fold (readableAlg classes sig))) 0 = true)
    (recursive : ∀ i fam source, args[i]? = some (.child fam source) →
      ∀ capture (member : (i, capture) ∈ σ),
      let depth := argDepth row.fam (.child fam) n (row.out.levelAt i)
      ReadableAt classes sig fam source depth →
      PrintedCaptureAt alg (path ++ [(args.take i).countP isChildArg]) depth fam source capture →
      PrintsTo sig depth fam source
        (eraseCapture row (args.map argSortOf) n σ child children block ⟨(i, capture), member⟩)) :
    ∀ i ta pa capture (member : (i, capture) ∈ σ),
      (atAddress path (args.map (ArgF.fold alg)) 0)[i]? = some ta →
      (args.map (ArgF.fold (printAlg sig)))[i]? = some pa →
      PrintEliminators.printArg sig ctx i
        (argDepth row.fam (argSortOf ta) n (row.out.levelAt i)) ta = .ok (some capture) →
      Templates.printArg sig (argDepth row.fam (argSortOf pa) n (row.out.levelAt i)) pa =
        .ok (some (eraseCapture row (args.map argSortOf) n σ child children block ⟨(i, capture), member⟩)) := by
  intro i ta pa capture member typedAt plainAt printed
  rw [List.getElem?_map] at plainAt
  obtain ⟨source, sourceAt, rfl⟩ := Option.map_eq_some_iff.mp plainAt
  have slot : (args.map argSortOf)[i]? = some (argSortOf source) := by
    simp only [List.getElem?_map, sourceAt, Option.map_some]
  cases source with
  | child fam source =>
    have atTyped := atAddress_fold_child_for alg path args i fam source sourceAt
    have typedEq := Option.some.inj (typedAt.symm.trans atTyped)
    subst ta
    have domain := argsReadable_at (args.map (ArgF.fold (readableAlg classes sig)))
      0 i (ArgF.fold (readableAlg classes sig) (.child fam source)) readable
      (by simp only [List.getElem?_map, sourceAt, Option.map_some])
    simp only [argSortOf, Nat.zero_add] at domain
    have sourcePrint : PrintedCaptureAt alg (path ++ [(args.take i).countP isChildArg])
        (argDepth row.fam (.child fam) n (row.out.levelAt i)) fam source capture := by
      apply printedCaptureAt_of_printArg
      exact printed
    have ordinary := recursive i fam source sourceAt capture member
      (readableAt_of_argReadable domain) sourcePrint
    exact printArg_child sig _ fam source _ ordinary
  | _ =>
    have atTyped := atAddress_fold_leaf_for alg sig path args i _
      (fun fam child eq => by cases eq) sourceAt
    have typedEq := Option.some.inj (typedAt.symm.trans atTyped)
    subst ta
    exact siteScalar_printArg sig ctx row (args.map argSortOf) n σ child children block
      i _ (fun fam child eq => by cases eq) slot capture member printed

end Effect4.Codegen


/-!
Pointwise successful typed argument printing supplies erased template captures.
Placement: exact-codecs R8; consumer: the generalized expression and statement source steps.
The existing ordinary readable print supplies its substitution independently.
This helper adds no whole-erasure premise to the public connector.
-/
set_option autoImplicit false
namespace Effect4.Codegen
open TypeScript Effect4.Program Template Templates
variable {Op : Type}

set_option maxHeartbeats 2000000 in
theorem eraseCaptures_siteArgs (sig : Signature Op) (ctx : PrintEliminators.Context Op)
    (row : Templates.Row) (sorts : List ArgSort) (n : Nat) (σ : Subst)
    (child : EffFam → Nat → (y : Expr) → (i : Nat) → (i, .expr y) ∈ σ → Expr)
    (children : EffFam → Nat → (ys : List Expr) → (i : Nat) → (i, .exprs ys) ∈ σ → List Expr)
    (block : Nat → (ss : List TypeScript.Stmt) → (i : Nat) → (i, .stmts ss) ∈ σ → List TypeScript.Stmt)
    (typedArgs plainArgs : List (ArgF Op Carrier)) (typedτ plainτ : Subst)
    (lengths : typedArgs.length = plainArgs.length)
    (typedPrint : PrintEliminators.printArgs sig ctx row.fam n row.out typedArgs 0 = .ok typedτ)
    (plainPrint : Templates.printArgs sig row.fam n row.out plainArgs 0 = .ok plainτ)
    (matched : ∀ i ∈ row.out.holes, lookup σ i = lookup typedτ i)
    (present : ∀ i ∈ row.out.holes, ∃ capture, lookup typedτ i = some capture)
    (slots : ∀ i ta pa capture (member : (i, capture) ∈ σ),
      i ∈ row.out.holes → typedArgs[i]? = some ta → plainArgs[i]? = some pa →
      PrintEliminators.printArg sig ctx i
        (argDepth row.fam (argSortOf ta) n (row.out.levelAt i)) ta = .ok (some capture) →
      Templates.printArg sig (argDepth row.fam (argSortOf pa) n (row.out.levelAt i)) pa =
        .ok (some (eraseCapture row sorts n σ child children block ⟨(i, capture), member⟩))) :
    ∀ i ∈ row.out.holes,
      lookup (eraseCaptures row sorts n σ child children block) i = lookup plainτ i := by
  intro i hole
  obtain ⟨capture, found⟩ := present i hole
  have matchFound : lookup σ i = some capture := (matched i hole).trans found
  have member := mem_of_lookup matchFound
  obtain ⟨k, item, index, itemAt, _⟩ :=
    PrintEliminators.printArgs_lookup_some ctx typedArgs 0 typedτ typedPrint i capture found
  simp only [Nat.zero_add] at index
  subst k
  have typedBound : i < typedArgs.length := (List.getElem?_eq_some_iff.mp itemAt).1
  have plainBound : i < plainArgs.length := by rwa [← lengths]
  let ta := typedArgs[i]'typedBound
  let pa := plainArgs[i]'plainBound
  have taAt : typedArgs[i]? = some ta := List.getElem?_eq_some_iff.mpr ⟨typedBound, rfl⟩
  have paAt : plainArgs[i]? = some pa := List.getElem?_eq_some_iff.mpr ⟨plainBound, rfl⟩
  have typedSlot := (PrintEliminators.printArgs_lookup ctx _ 0 typedτ typedPrint).1 i ta taAt
  rw [Nat.zero_add, found] at typedSlot
  have erasedSlot := slots i ta pa capture member hole taAt paAt typedSlot
  have plainSlot := (printArgs_lookup _ 0 plainτ plainPrint).1 i pa paAt
  rw [Nat.zero_add] at plainSlot
  have result := Except.ok.inj (erasedSlot.symm.trans plainSlot)
  rw [eraseCaptures_lookup row sorts n σ child children block matchFound member]
  exact result

end Effect4.Codegen

set_option autoImplicit false
namespace Effect4.Codegen
open TypeScript Effect4.Program Template Templates
variable {Op : Type} {classes : Classes.Classes} {sig : Signature Op}
  {spell : String → List RowArg → Option Op}
/-! Placement: exact-codecs R8; actual typed-site rigid row reconstruction.
Consumer: full source/address erasure induction.
Only smaller captured outputs enter the recursive premises. -/
set_option maxHeartbeats 2000000 in
theorem eraseExprRow_site_rigid (alg : EffAlgebra Op TCarrier) (ctx : PrintEliminators.Context Op) {fam : EffFam} {path : List Nat} {n : Nat}
    {args : List (ArgF Op (EffSelfCarrier Op))} {ctor : String}
    {row : Templates.Row} {t : Tpl} {τ : Subst} {x plain : Expr} {τplain : Subst}
    (_member : row ∈ Templates.table) (selected : row.selects fam ctor args = true)
    (sorts : argSorts row.fam row.ctor = some (args.map argSortOf))
    (output : row.out = .tpl t) (rigid : t.rigid = true)
    (printed : PrintEliminators.printArgs sig ctx row.fam n row.out
      (atAddress path (args.map (ArgF.fold (alg))) 0) 0 = .ok τ)
    (instantiated : inst n τ t = some x)
    (readable : argsReadable classes sig row.fam n row.out (rowDaemon row)
      (args.map (ArgF.fold (readableAlg classes sig))) 0 = true)
    (ordinaryArgs : printArgs sig row.fam n row.out (args.map (ArgF.fold (printAlg sig))) 0 = .ok τplain)
    (ordinaryInst : inst n τplain t = some plain)
    (hchild : ∀ i fam d (source : EffSelfCarrier Op fam) y,
      args[i]? = some (.child fam source) →
      d = argDepth row.fam (.child fam) n (row.out.levelAt i) →
      sizeOf y < sizeOf x → ReadableAt classes sig fam source d →
      PrintedCaptureAt alg (path ++ [(args.take i).countP isChildArg]) d fam source (.expr y) →
      PrintsTo sig d fam source (.expr ((eraseT classes sig spell fam d y).getD y)))
    (hchildren : ∀ i fam d (source : EffSelfCarrier Op fam) ys,
      args[i]? = some (.child fam source) →
      d = argDepth row.fam (.child fam) n (row.out.levelAt i) →
      sizeOf ys < sizeOf x → ReadableAt classes sig fam source d →
      PrintedCaptureAt alg (path ++ [(args.take i).countP isChildArg]) d fam source (.exprs ys) →
      PrintsTo sig d fam source (.exprs (eraseSpine classes sig spell fam d ys)))
    (hblock : ∀ i d (source : Stmts Op) ss,
      args[i]? = some (.child .stmts source) →
      d = argDepth row.fam (.child .stmts) n (row.out.levelAt i) →
      sizeOf ss < sizeOf x → ReadableAt classes sig .stmts source d →
      PrintedCaptureAt alg (path ++ [(args.take i).countP isChildArg]) d .stmts source (.stmts ss) →
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
      PrintedCaptureAt alg (path ++ [(args.take i).countP isChildArg]) depth fam source capture →
      PrintsTo sig depth fam source
        (eraseCapture row (args.map argSortOf) n σ child' children' block' ⟨(i, capture), member⟩) := by
    intro i fam source sourceAt capture member depth hread htyped
    have hslot : (args.map argSortOf)[i]? = some (.child fam) := by
      simp only [List.getElem?_map, sourceAt, Option.map_some, argSortOf]
    cases capture with
    | expr y =>
      simpa only [eraseCapture, hslot, Option.getD_some, child'] using
        hchild i fam depth source y sourceAt rfl (match_below n t x σ rigid matched (i, .expr y) member) hread htyped
    | exprs ys =>
      simpa only [eraseCapture, hslot, Option.getD_some, children'] using
        hchildren i fam depth source ys sourceAt rfl (match_below n t x σ rigid matched (i, .exprs ys) member) hread htyped
    | stmts ss =>
      have hfam : fam = .stmts := by
        cases fam <;> simp only [PrintedCaptureAt] at htyped ⊢
      subst fam
      simpa only [eraseCapture, hslot, Option.getD_some, block'] using
        hblock i depth source ss sourceAt rfl (match_below n t x σ rigid matched (i, .stmts ss) member) hread htyped
    | _ => cases fam <;> cases htyped
  have erasedAgree := eraseCaptures_siteArgs sig ctx row (args.map argSortOf) n σ
    child' children' block'
    (atAddress path (args.map (ArgF.fold alg)) 0)
    (args.map (ArgF.fold (printAlg sig))) τ τplain
    (by simp only [length_atAddress, List.length_map]) printed ordinaryArgs hmatched
    (fun i hi => holes_of_inst n τ t x instantiated i (by rwa [output] at hi))
    (fun i ta pa capture member _ typedAt plainAt printed =>
      source_site_slot_transport classes sig alg path ctx row n args σ child' children' block'
        readable recursive i ta pa capture member typedAt plainAt printed)
  exact eraseExprRow_rigid_inst classes sig spell fam n x row child children block
    (fun fam' _ d => eraseT classes sig spell fam' d x) family output sortsFam matched rigid ordinaryInst
    (fun i hi => erasedAgree i (by rwa [output]))

end Effect4.Codegen

set_option autoImplicit false
namespace Effect4.Codegen
open TypeScript Effect4.Program Template Templates
variable {Op : Type} {classes : Classes.Classes} {sig : Signature Op}
/-! Placement: exact-codecs R8; first-match rigid row separation.
Consumer: expression node reconstruction in the successful full typed print. -/
set_option maxHeartbeats 2000000 in
theorem site_child_at_hole (alg : EffAlgebra Op TCarrier) (ctx : PrintEliminators.Context Op) {fam : EffFam} {n : Nat} {path : List Nat}
    {row : Templates.Row} {args : List (ArgF Op (EffSelfCarrier Op))}
    {t : Tpl} {τ : Subst} {x : Expr}
    (_output : row.out = .tpl t) (_family : row.fam = fam) (rigid : t.rigid = true)
    (printed : PrintEliminators.printArgs sig ctx fam n (.tpl t)
      (atAddress path (args.map (ArgF.fold (alg))) 0) 0 = .ok τ)
    (instantiated : inst n τ t = some x)
    (readable : argsReadable classes sig fam n (.tpl t) (rowDaemon row)
      (args.map (ArgF.fold (readableAlg classes sig))) 0 = true)
    (recursive : ∀ i fam d (source : EffSelfCarrier Op fam) y,
      args[i]? = some (.child fam source) →
      d = argDepth row.fam (.child fam) n (row.out.levelAt i) →
      sizeOf y < sizeOf x → ReadableAt classes sig fam source d →
      PrintedCaptureAt alg (path ++ [(args.take i).countP isChildArg]) d fam source (.expr y) → nodeLike y = true)
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
      have addressed := atAddress_fold_child_for alg path args i childFam source sourceAt
      have hp := (PrintEliminators.printArgs_lookup ctx _ 0 τ printed).1 i _ addressed
      rw [Nat.zero_add, argSortOf, look] at hp
      exact recursive i childFam _ source y sourceAt (by rw [_family, _output]; rfl) smaller (readableAt_of_argReadable domain)
        (printedCaptureAt_of_printArg hp)
    | _ => exact absurd child Bool.false_ne_true

end Effect4.Codegen


namespace Effect4.Codegen.PrintEliminators
open Effect4.Program
variable {Op : Type}

-- Placement: exact-codecs R8, actual-context depth for the full typed-print erasure claim.
-- Consumer: the typed site certificate's child fields. Layers use the existing closed family rule.
def childScope (n : Nat) (node : Node Op) (i : Nat) : Nat :=
  match node.child i with
  | some (.layer _) | some (.layers _) => 0
  | _ => node.childLevel n i

-- Successful environment maps determine the added length before the node cases unfold.
-- Consumer: childEnv_length's continuation cases.
theorem env_append_one_map_length {A : Type} (source : Option A) (env : TyEnv)
    (value : A → Ty) {rho : NodeEnv}
    (found : source.map (fun a => NodeEnv.env (env ++ [value a])) = some rho) :
    rho.tyEnv.length = env.length + 1 := by
  obtain ⟨a, _, assembled⟩ := Option.map_eq_some_iff.mp found
  cases assembled
  simp only [NodeEnv.tyEnv, List.length_append, List.length_cons, List.length_nil]

theorem env_append_two_map_length {A : Type} (source : Option A) (env : TyEnv)
    (first second : A → Ty) {rho : NodeEnv}
    (found : source.map (fun a => NodeEnv.env (env ++ [first a, second a])) = some rho) :
    rho.tyEnv.length = env.length + 2 := by
  obtain ⟨a, _, assembled⟩ := Option.map_eq_some_iff.mp found
  cases assembled
  simp only [NodeEnv.tyEnv, List.length_append, List.length_cons, List.length_nil]

theorem body_append_one_map_length {A : Type} (source : Option A) (env : TyEnv)
    (value : A → Ty) (loop : Bool) {rho : NodeEnv}
    (found : source.map (fun a => NodeEnv.body (env ++ [value a]) loop) = some rho) :
    rho.tyEnv.length = env.length + 1 := by
  obtain ⟨a, _, assembled⟩ := Option.map_eq_some_iff.mp found
  cases assembled
  simp only [NodeEnv.tyEnv, List.length_append, List.length_cons, List.length_nil]

-- The select map's actual arm lengths are proved by the existing decision law.
theorem select_left_map_length (s : Signature Op) (env : TyEnv) (term : Term)
    (decision : Decision) {rho : NodeEnv}
    (found : ((termTy s env term).bind decision.arms).map
      (fun arms => NodeEnv.env (env ++ arms.1)) = some rho) :
    rho.tyEnv.length = env.length + decision.binds.1 := by
  obtain ⟨arms, harm, assembled⟩ := Option.map_eq_some_iff.mp found
  obtain ⟨ty, _, harms⟩ := Option.bind_eq_some_iff.mp harm
  cases assembled
  simp only [NodeEnv.tyEnv, List.length_append]
  exact congrArg (env.length + ·) (congrArg Prod.fst
    (Decision.arms_length decision ty arms.1 arms.2 harms))

theorem select_right_map_length (s : Signature Op) (env : TyEnv) (term : Term)
    (decision : Decision) {rho : NodeEnv}
    (found : ((termTy s env term).bind decision.arms).map
      (fun arms => NodeEnv.env (env ++ arms.2)) = some rho) :
    rho.tyEnv.length = env.length + decision.binds.2 := by
  obtain ⟨arms, harm, assembled⟩ := Option.map_eq_some_iff.mp found
  obtain ⟨ty, _, harms⟩ := Option.bind_eq_some_iff.mp harm
  cases assembled
  simp only [NodeEnv.tyEnv, List.length_append]
  exact congrArg (env.length + ·) (congrArg Prod.snd
    (Decision.arms_length decision ty arms.1 arms.2 harms))

theorem childScope_select_left (n : Nat) (term : Term) (decision : Decision)
    (left right : Eff Op) :
    childScope n (.eff (.select term decision left right)) 0 = n + decision.binds.1 := by
  cases decision <;> rfl

theorem childScope_select_right (n : Nat) (term : Term) (decision : Decision)
    (left right : Eff Op) :
    childScope n (.eff (.select term decision left right)) 1 = n + decision.binds.2 := by
  cases decision <;> rfl

-- Each function case has a fixed scope. The map facts avoid unfolding checker answers.
-- No selected template or whole-program typing premise enters this calculation.
set_option maxHeartbeats 600000 in
theorem childEnv_length (s : Signature Op) (parent : NodeEnv) (node : Node Op) (i : Nat)
    {rho : NodeEnv} (found : node.childEnv s parent i = some rho) :
    rho.tyEnv.length = childScope parent.tyEnv.length node i := by
  fun_cases Node.childEnv s parent node i
  case case24 term decision left right =>
    simp only [Node.childEnv] at found
    rw [childScope_select_left]
    exact select_left_map_length s parent.tyEnv term decision found
  case case25 term decision left right =>
    simp only [Node.childEnv] at found
    rw [childScope_select_right]
    exact select_right_map_length s parent.tyEnv term decision found
  -- An invocation's programs and their spine (decisions row 340), by hand: a search over the
  -- spine's catch-all on the parent reaches `Classical.choice`.
  case case28 k request args =>
    simp only [Node.childEnv] at found
    obtain ⟨d, _, invoked⟩ := Option.bind_eq_some_iff.mp found
    cases params : d.params with
    | nil => rw [params] at invoked; cases invoked
    | cons q qs =>
      rw [params] at invoked
      cases invoked
      simp only [NodeEnv.tyEnv, List.length_append, List.length_singleton]
      rfl
  case case52 head tail =>
    simp only [Node.childEnv] at found
    cases found
    cases parent with
    | slots tys qs => cases qs <;> rfl
    | env tys => rfl
    | body tys loop => rfl
    | closed => rfl
  case case53 head tail tys q0 q qs =>
    simp only [Node.childEnv] at found
    cases found
    simp only [NodeEnv.tyEnv, List.length_append, List.length_singleton]
    rfl
  case case54 head tail env qs notTwo =>
    cases qs with
    | nil => simp only [Node.childEnv, reduceCtorEq] at found
    | cons q0 rest =>
      cases rest with
      | nil => simp only [Node.childEnv, reduceCtorEq] at found
      | cons q qs => exact (notTwo q0 q qs rfl).elim
  case case55 head tail notTwo notSlots =>
    cases parent with
    | slots tys qs => exact (notSlots tys qs rfl).elim
    | env tys => simp only [Node.childEnv] at found; cases found; rfl
    | body tys loop => simp only [Node.childEnv] at found; cases found; rfl
    | closed => simp only [Node.childEnv] at found; cases found; rfl
  all_goals
    aesop (add norm simp [Node.childEnv, childScope, Node.child, Node.childLevel,
      Node.binders, Node.closedChild, NodeEnv.tyEnv])
      (add safe forward [env_append_one_map_length, env_append_two_map_length,
        body_append_one_map_length])

end Effect4.Codegen.PrintEliminators


namespace Effect4.Codegen.PrintEliminators
open Effect4.Program TypeScript Templates
variable {Op : Type}

-- Placement: exact-codecs R8, actual-context child-depth step.
-- Consumer: sourceChildScope_templateDepth, then successful typed-site capture induction.
-- These helpers read existing source views and finite table metadata only.

def decisionPatternBinds : ArgPat → Option (Nat × Nat)
  | .is (.decision .bool) => some (0,0)
  | .is (.decision .option) => some (0,1)
  | .decisionTag | .decisionRecordTag => some (1,1)
  | _ => none

def constructorChildOffset (ctor : String) (binds : Nat × Nat) (i : Nat) : Nat :=
  if ctor = "bind" ∨ ctor = "catchCause" ∨ ctor = "onExit" then
    if i = 1 then 1 else 0
  else if ctor = "matchCause" then
    if i = 1 ∨ i = 2 then 1 else 0
  else if ctor = "catchIf" then
    if i = 2 then 1 else 0
  else if ctor = "acquireRelease" then
    if i = 1 then 2 else 0
  else if ctor = "iterate" then
    if i = 5 then 1 else 0
  else if ctor = "select" then
    if i = 2 then binds.1 else if i = 3 then binds.2 else 0
  else 0

def sourceChildOffset (ctor : String) (args : List (ArgF Op (EffSelfCarrier Op))) (i : Nat) : Nat :=
  constructorChildOffset ctor ((args[1]?.bind fun arg => match arg with
    | .decision d => some d.binds
    | _ => none).getD (0,0)) i

def rowDecisionBinds (row : Templates.Row) : Option (Nat × Nat) :=
  (row.fixed.find? fun fixed => decide (fixed.1 = 1)).bind fun fixed => decisionPatternBinds fixed.2

def rowChildOffset (row : Templates.Row) (i : Nat) : Nat :=
  constructorChildOffset row.ctor (rowDecisionBinds row |>.getD (0,0)) i

def rowChildDepthOK (row : Templates.Row) : Bool :=
  ((Effect4.Program.argSorts row.fam row.ctor).getD []).zipIdx.all fun pair =>
    match pair.1 with
    | .child _ => match row.fam with
      | .eff => decide (row.out.levelAt pair.2 = rowChildOffset row pair.2)
      | .action | .stmt => decide (row.out.levelAt pair.2 = 0)
      | .layer | .layers | .effs | .stmts => true
    | _ => true

def rowSelectClassifierOK (row : Templates.Row) : Bool :=
  if row.fam = .eff ∧ row.ctor = "select" then (rowDecisionBinds row).isSome else true

theorem table_childDepths : Templates.table.all rowChildDepthOK = true := by decide

theorem table_selectClassifier : Templates.table.all rowSelectClassifierOK = true := by decide

-- The classifier fixes the same binder count that the source decision owns.
-- This four-pattern proof never unfolds the production table.
theorem decisionPatternBinds_holds {R : EffFam → Type} (pattern : ArgPat)
    (arg : ArgF Op R) (binds : Nat × Nat)
    (recognized : decisionPatternBinds pattern = some binds) (holds : pattern.holds arg = true) :
    ∃ decision, arg = .decision decision ∧ decision.binds = binds := by
  fun_cases decisionPatternBinds pattern <;>
    aesop (add norm simp [decisionPatternBinds, ArgPat.holds, Fixed.holds, Decision.binds, decide_eq_true_eq])

-- The selected row's fixed pattern answers at actual argument one.
-- The only source-dependent template offset is select's decision binder pair.
theorem rowDecisionBinds_selected (row : Templates.Row)
    (args : List (ArgF Op (EffSelfCarrier Op))) (pair : Nat × Nat)
    (selected : row.selects .eff "select" args = true)
    (recognized : rowDecisionBinds row = some pair) :
    ∃ decision, args[1]? = some (.decision decision) ∧ decision.binds = pair := by
  unfold rowDecisionBinds at recognized
  obtain ⟨fixed, found, binds⟩ := Option.bind_eq_some_iff.mp recognized
  have member := List.mem_of_find?_eq_some found
  have test := List.find?_some found
  have index : fixed.1 = 1 := of_decide_eq_true test
  have selectedFixed : row.fixed.all (fun fixed => patternAt args fixed.1 fixed.2) = true := by
    unfold Templates.Row.selects at selected
    exact (Bool.and_eq_true_iff.mp selected).2
  have fixedHolds := List.all_eq_true.mp selectedFixed fixed member
  unfold patternAt at fixedHolds
  rw [index] at fixedHolds
  cases got : args[1]? with
  | none => rw [got] at fixedHolds; cases fixedHolds
  | some arg =>
    rw [got] at fixedHolds
    obtain ⟨decision, harg, count⟩ := decisionPatternBinds_holds fixed.2 arg pair binds fixedHolds
    exact ⟨decision, congrArg some harg, count⟩

-- Non-select constructor offsets do not read a decision argument.
theorem constructorChildOffset_nonselect (ctor : String) (i : Nat) (a b : Nat × Nat)
    (other : ctor ≠ "select") :
    constructorChildOffset ctor a i = constructorChildOffset ctor b i := by
  aesop (add norm simp [constructorChildOffset, other])

theorem rowChildOffset_source (row : Templates.Row) (member : row ∈ Templates.table)
    (args : List (ArgF Op (EffSelfCarrier Op)))
    (selected : row.selects .eff row.ctor args = true) (i : Nat) :
    rowChildOffset row i = sourceChildOffset row.ctor args i := by
  by_cases select : row.ctor = "select"
  · have family := (selects_fam_ctor selected).1
    have checked := List.all_eq_true.mp table_selectClassifier row member
    simp only [rowSelectClassifierOK, family, select, and_self, ↓reduceIte] at checked
    obtain ⟨pair, pairFound⟩ := Option.isSome_iff_exists.mp checked
    obtain ⟨decision, got, count⟩ := rowDecisionBinds_selected row args pair
      (by simpa only [select] using selected) pairFound
    simp only [rowChildOffset, sourceChildOffset, pairFound, got, Option.bind_some,
      Option.getD_some, count]
  · exact constructorChildOffset_nonselect row.ctor i _ _ select

-- Generated source fields fix each child ordinal before it reaches a selected row.
-- The source has at most six declaration arguments, as its generated view proves below.
-- Splitting those indices makes each constructor proof a closed list calculation.
-- No template table or successful typing premise enters this source metadata calculation.
-- A definition block is excluded: its bodies bind the request, and its row is a refusal.
-- An invocation is excluded too: its programs bind their parameter's request, and its row refuses.
theorem view_eff_child_binders (source : Eff Op) (i : Nat) (childFam : EffFam)
    (child : EffSelfCarrier Op childFam)
    (notBlock : ∀ decls bodies main, source ≠ Eff.defs decls bodies main)
    (notInvoke : ∀ k request programs, source ≠ Eff.invoke k request programs)
    (captured : (view_eff source).2[i]? = some (.child childFam child)) :
    (Node.eff source).binders (((view_eff source).2.take i).countP isChildArg) =
      sourceChildOffset (view_eff source).1 (view_eff source).2 i := by
  have arity : (view_eff source).2.length ≤ 6 := by
    fun_cases view_eff source <;>
      simp only [List.length_cons, List.length_nil] <;> omega
  obtain ⟨indexBound, -⟩ := List.getElem?_eq_some_iff.mp captured
  have casesIndex : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases casesIndex with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    cases source with
    | select scrutinee decision left right =>
      cases decision <;> cases captured <;> rfl
    | defs decls bodies main => exact absurd rfl (notBlock decls bodies main)
    | invoke k request programs => exact absurd rfl (notInvoke k request programs)
    | _ => cases captured <;> rfl

-- Only clause families own rows; spines use their existing list rules.
def rowClauseFamily (row : Templates.Row) : Bool :=
  decide (row.fam = .eff ∨ row.fam = .action ∨ row.fam = .stmt ∨ row.fam = .layer)

theorem table_clauseFamilies : Templates.table.all rowClauseFamily = true := by decide

-- The invocation's row refuses: no skeleton prints its programs yet (decisions row 340).
-- Consumer: childEnv_template_depth, which excludes an invocation by it.
def rowInvokeRefused (row : Templates.Row) : Bool :=
  match row.out with
  | .refuse _ => true
  | _ => row.ctor != "invoke"

theorem table_invokeRefused : Templates.table.all rowInvokeRefused = true := by decide

theorem table_childDepth_at {row : Templates.Row} (member : row ∈ Templates.table)
    {sorts : List ArgSort} (hsorts : Effect4.Program.argSorts row.fam row.ctor = some sorts)
    {i : Nat} {childFam : EffFam} (captured : sorts[i]? = some (.child childFam)) :
    match row.fam with
    | .eff => row.out.levelAt i = rowChildOffset row i
    | .action | .stmt => row.out.levelAt i = 0
    | .layer | .layers | .effs | .stmts => True := by
  have rows := List.all_eq_true.mp table_childDepths row member
  simp only [rowChildDepthOK, hsorts, Option.getD_some, List.all_eq_true] at rows
  have zipped : (.child childFam, i) ∈ sorts.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr captured
  have here := rows (.child childFam, i) zipped
  cases hf : row.fam with
  | eff => simp only [hf] at here; exact of_decide_eq_true here
  | stmt => simp only [hf] at here; exact of_decide_eq_true here
  | stmts => exact True.intro
  | effs => exact True.intro
  | action => simp only [hf] at here; exact of_decide_eq_true here
  | layer => exact True.intro
  | layers => exact True.intro

end Effect4.Codegen.PrintEliminators


-- Prelude: checked context-small-laws, ChildEnvLength, SourceDepthMetadata,
-- plus host's SiteSourceFocus. This section introduces no duplicated source representation.
namespace Effect4.Codegen.PrintEliminators
open Effect4.Program Templates
variable {Op : Type}

-- Placement: exact-codecs R8, typed-site erasure actual-context step.
-- Consumer: childEnv_template_depth, which excludes a definition block by it.
theorem childEnv_block_none (s : Signature Op) (parent : NodeEnv) (decls : List DefDecl)
    (bodies : Effs Op) (main : Eff Op) (j : Nat) :
    (Node.eff (.defs decls bodies main)).childEnv s parent j = none := by
  cases j with
  | zero => rfl
  | succ j =>
    cases j with
    | zero => rfl
    | succ j =>
      cases j with
      | zero => rfl
      | succ j => rfl

-- Placement: exact-codecs R8, typed-site erasure actual-context step.
-- Consumer: actual source-image predicate at each recursive template child.
theorem childEnv_layer_zero (s : Signature Op) (parent : NodeEnv)
    (source : LayerTerm Op) (j : Nat) {rho : NodeEnv}
    (found : (Node.layer source).childEnv s parent j = some rho) : rho.tyEnv.length = 0 := by
  cases source <;> cases j with
  | zero => simp only [Node.childEnv] at found; cases found <;> rfl
  | succ j =>
    cases j with
    | zero => simp only [Node.childEnv] at found; cases found <;> rfl
    | succ j => simp only [Node.childEnv] at found; cases found


-- No whole-program typing premise enters this equation.
-- Actual successful childEnv and selected source view fix both sides.
theorem childEnv_template_depth
    (s : Signature Op) (parent : NodeEnv)
    (fam : EffFam) (source : EffSelfCarrier Op fam)
    (ctor : String) (args : List (ArgF Op (EffSelfCarrier Op)))
    (row : Templates.Row) (i : Nat) (childFam : EffFam)
    (child : EffSelfCarrier Op childFam) {rho : NodeEnv}
    (viewed : view fam source = (ctor,args))
    (selected : (Templates.table.find? fun row => row.selects fam ctor args) = some row)
    (captured : args[i]? = some (.child childFam child))
    (found : (Effect4.Codegen.nodeOfFamily fam source).childEnv s parent
      ((args.take i).countP isChildArg) = some rho)
    (printing : ∀ name, row.out ≠ .refuse name) :
    rho.tyEnv.length = argDepth fam (.child childFam) parent.tyEnv.length (row.out.levelAt i) := by
  have member := List.mem_of_find?_eq_some selected
  have selector := List.find?_some selected
  obtain ⟨family, constructor⟩ := selects_fam_ctor selector
  have sorts : Effect4.Program.argSorts row.fam row.ctor = some (args.map argSortOf) := by
    rw [family, constructor]
    have sourceSorts := argSorts_view fam source
    rw [viewed] at sourceSorts
    exact sourceSorts
  have sortAt : (args.map argSortOf)[i]? = some (.child childFam) := by
    simp only [List.getElem?_map, captured, Option.map_some, argSortOf]
  have level := table_childDepth_at member sorts sortAt
  have actualChild := Effect4.Codegen.source_child_of_view viewed captured
  have familyKind : fam = .eff ∨ fam = .action ∨ fam = .stmt ∨ fam = .layer := by
    have h := List.all_eq_true.mp table_clauseFamilies row member
    have h' := of_decide_eq_true h
    rwa [family] at h'
  rcases familyKind with rfl | rfl | rfl | rfl
  · change view_eff source = (ctor,args) at viewed
    have notBlock : ∀ decls bodies main, source ≠ Eff.defs decls bodies main := by
      rintro decls bodies main rfl
      have stops := childEnv_block_none s parent decls bodies main ((args.take i).countP isChildArg)
      exact nomatch stops.symm.trans found
    have notInvoke : ∀ k request programs, source ≠ Eff.invoke k request programs := by
      rintro k request programs rfl
      have refused := List.all_eq_true.mp table_invokeRefused row member
      have named : row.ctor = "invoke" := constructor.trans (congrArg Prod.fst viewed).symm
      unfold rowInvokeRefused at refused
      cases out : row.out with
      | refuse name => exact printing name out
      | _ => simp only [out, named, bne_self_eq_false, Bool.false_eq_true] at refused
    have binder := view_eff_child_binders source i childFam child notBlock notInvoke
      (by rw [viewed]; exact captured)
    have offset := rowChildOffset_source row member args
      (by simpa only [constructor] using selector) i
    simp only [family] at level
    have binderLevel : (Node.eff source).binders ((args.take i).countP isChildArg) =
        row.out.levelAt i := by
      rw [viewed] at binder
      rw [constructor] at offset
      exact binder.trans (offset.symm.trans level.symm)
    rw [childEnv_length s parent _ _ found]
    rw [childScope, actualChild]
    cases childFam <;>
      simp only [Effect4.Codegen.nodeOfFamily,
        Node.childLevel, Node.closedChild, binderLevel, argDepth, Bool.false_eq_true, ↓reduceIte]
  · simp only [family] at level
    rw [childEnv_length s parent _ _ found]
    rw [childScope, actualChild]
    cases childFam <;>
      simp only [Effect4.Codegen.nodeOfFamily,
        Node.childLevel, Node.closedChild, Node.binders, argDepth, level, Nat.add_zero, Bool.false_eq_true, ↓reduceIte]
  · simp only [family] at level
    rw [childEnv_length s parent _ _ found]
    rw [childScope, actualChild]
    cases childFam <;>
      simp only [Effect4.Codegen.nodeOfFamily,
        Node.childLevel, Node.closedChild, Node.binders, argDepth, level, Nat.add_zero, Bool.false_eq_true, ↓reduceIte]
  · exact childEnv_layer_zero s parent source _ found

end Effect4.Codegen.PrintEliminators


set_option autoImplicit false
namespace Effect4.Codegen
open TypeScript Effect4.Program Template Templates
variable {Op : Type}

/-- Successful site printing supplies the actual context at its source address.
Placement: exact-codecs R8; consumer: source focus of recursive template captures. -/
theorem printedCaptureAt_context {sig : Signature Op} {ann : List Nat → Option (List Ty)}
    {contexts : List Nat → Option (PrintEliminators.Context Op)}
    {fam : EffFam} {source : EffSelfCarrier Op fam} {path : List Nat} {n : Nat} {capture : Arg}
    (printed : PrintedCaptureAt (typedSitesAlg sig ann contexts) path n fam source capture) :
    ∃ ctx, contexts path = some ctx := by
  obtain ⟨ctor, args, viewed⟩ : ∃ ctor args, view fam source = (ctor, args) := ⟨_, _, rfl⟩
  have built : build fam ctor args = some source := by
    have h := build_view fam source
    rwa [viewed] at h
  have equation := cata_build
    (fun fam ctor args path => match contexts path with
      | some ctx => PrintEliminators.layer sig ctx (ann path) fam ctor (atAddress path args 0)
      | none => PrintEliminators.missing fam) fam ctor args source built
  cases found : contexts path with
  | some ctx => exact ⟨ctx, rfl⟩
  | none =>
    cases fam <;> cases capture <;>
      simp only [PrintedCaptureAt] at printed <;>
      (simp only [cataFam] at equation;
        have equationAt := congrFun (congrFun equation path) n;
        have impossible := equationAt.symm.trans printed;
        rw [found] at impossible; cases impossible)

/-- The actual child context and selected template determine the child environment depth.
Placement: exact-codecs R8; consumer: the recursive capture step of typed-site erasure. -/
theorem siteFocused_child {sig : Signature Op} {root : Eff Op} {env0 : TyEnv}
    {path : List Nat} {fam : EffFam} {source : EffSelfCarrier Op fam} {n : Nat}
    {ctor : String} {args : List (ArgF Op (EffSelfCarrier Op))} {row : Templates.Row}
    {i : Nat} {childFam : EffFam} {child : EffSelfCarrier Op childFam}
    {ctx : PrintEliminators.Context Op}
    (focus : SiteFocused root sig env0 path fam source n)
    (viewed : view fam source = (ctor, args))
    (selected : Templates.table.find? (fun row => row.selects fam ctor args) = some row)
    (captured : args[i]? = some (.child childFam child))
    (found : PrintEliminators.contextAtTable (annotate sig env0 root) root
      (path ++ [(args.take i).countP isChildArg]) = some ctx)
    (printing : ∀ name, row.out ≠ .refuse name) :
    SiteFocused root sig env0 (path ++ [(args.take i).countP isChildArg]) childFam child
      (argDepth fam (.child childFam) n (row.out.levelAt i)) := by
  obtain ⟨sourceAt, parent, parentAt, parentLength, _⟩ := focus
  have step := source_child_of_view viewed captured
  have childAt := Node.at_child sourceAt step
  obtain ⟨_, rho, rhoAt, _, _, _⟩ :=
    PrintEliminators.contextAtTable_annotate_facts found
  have envStep : (nodeOfFamily fam source).childEnv sig parent
      ((args.take i).countP isChildArg) = some rho := by
    rw [Node.envAt_append, sourceAt, parentAt] at rhoAt
    simp only [Option.bind_some, Node.envAt, step] at rhoAt
    cases environment : (nodeOfFamily fam source).childEnv sig parent
        ((args.take i).countP isChildArg) with
    | none => rw [environment] at rhoAt; cases rhoAt
    | some rho' => simpa only [environment, Option.bind_some] using rhoAt
  have depth := PrintEliminators.childEnv_template_depth sig parent fam source ctor args row i
    childFam child viewed selected captured envStep printing
  rw [parentLength] at depth
  refine ⟨childAt, rho, rhoAt, depth, ?_⟩
  cases childFam with
  | layer => cases fam <;> rfl
  | layers => cases fam <;> rfl
  | _ => exact True.intro

end Effect4.Codegen


set_option autoImplicit false
namespace Effect4.Codegen
open TypeScript Effect4.Program Template Templates
variable {Op : Type}

/-- The generated fold exposes the existing site layer at its actual source address.
Placement: exact-codecs R8; consumer: expression and statement template inversion. -/
theorem typedSites_cata_build (sig : Signature Op) (ann : List Nat → Option (List Ty))
    (contexts : List Nat → Option (PrintEliminators.Context Op))
    (fam : EffFam) (ctor : String) (args : List (ArgF Op (EffSelfCarrier Op)))
    (source : EffSelfCarrier Op fam) (built : build fam ctor args = some source)
    (path : List Nat) :
    cataFam (typedSitesAlg sig ann contexts) fam source path =
      match contexts path with
      | some ctx => PrintEliminators.layer sig ctx (ann path) fam ctor
          (atAddress path (args.map (ArgF.fold (typedSitesAlg sig ann contexts))) 0)
      | none => PrintEliminators.missing fam := by
  let layer : (fam : EffFam) → String → List (ArgF Op TCarrier) → TCarrier fam :=
    fun fam ctor args path => match contexts path with
      | some ctx => PrintEliminators.layer sig ctx (ann path) fam ctor (atAddress path args 0)
      | none => PrintEliminators.missing fam
  exact congrFun (cata_build layer fam ctor args source built) path

/-- A successful template site exposes its captures before the finite node decoration.
Placement: exact-codecs R8; consumer: normalized expression-row reconstruction. -/
theorem site_template_inv {sig : Signature Op} {ann : List Nat → Option (List Ty)}
    {contexts : List Nat → Option (PrintEliminators.Context Op)}
    {fam : EffFam} {source : EffSelfCarrier Op fam} {path : List Nat} {n : Nat} {x : Expr}
    {ctor : String} {args : List (ArgF Op (EffSelfCarrier Op))} {row : Templates.Row} {t : Tpl}
    (family : fam = .eff ∨ fam = .action ∨ fam = .layer)
    (built : build fam ctor args = some source)
    (selected : Templates.table.find? (fun row => row.selects fam ctor args) = some row)
    (output : row.out = .tpl t)
    (printed : PrintedCaptureAt (typedSitesAlg sig ann contexts) path n fam source (.expr x)) :
    ∃ ctx τ y, contexts path = some ctx ∧
      PrintEliminators.printArgs sig ctx fam n (.tpl t)
        (atAddress path (args.map (ArgF.fold (typedSitesAlg sig ann contexts))) 0) 0 = .ok τ ∧
      inst n τ t = some y ∧ PrintEliminators.decorate sig ctx y = .ok x := by
  obtain ⟨ctx, found⟩ := printedCaptureAt_context printed
  have selectTyped : Templates.table.find? (fun row => row.selects fam ctor
      (atAddress path (args.map (ArgF.fold (typedSitesAlg sig ann contexts))) 0)) = some row := by
    simpa only [selects_atAddress, selects_fold] using selected
  have equation := typedSites_cata_build sig ann contexts fam ctor args source built path
  have actual : (do
      let τ ← PrintEliminators.printArgs sig ctx fam n (.tpl t)
        (atAddress path (args.map (ArgF.fold (typedSitesAlg sig ann contexts))) 0) 0
      let y ← PrintEliminators.need ctor (inst n τ t)
      PrintEliminators.decorate sig ctx y) = .ok x := by
    rcases family with rfl | rfl | rfl <;>
      simp only [PrintedCaptureAt] at printed <;>
      (simp only [cataFam] at equation;
        rw [equation, found] at printed;
        simpa only [PrintEliminators.layer, selectTyped, output] using printed)
  obtain ⟨τ, arguments, remainder⟩ := bind_eq_ok.mp actual
  obtain ⟨y, instantiated, decorated⟩ := bind_eq_ok.mp remainder
  have instantiated' : inst n τ t = some y := by
    cases foundValue : inst n τ t with
    | none => simp only [PrintEliminators.need, foundValue] at instantiated; cases instantiated
    | some value =>
      simp only [PrintEliminators.need, foundValue, Except.ok.injEq] at instantiated
      exact congrArg some instantiated
  exact ⟨ctx, τ, y, found, arguments, instantiated', decorated⟩

end Effect4.Codegen


/-!
Placement: exact-codecs, R8, helper of successful typed-site erasure.
Consumer: the generalized statement-spine step and the full source-image erasure theorem.
Reach: existing readable statement syntax, actual context addresses, successful typed printing.
The smaller-target recursive callbacks retain actual source focus and ordinary readability.
This proves syntax reconstruction only; no TypeScript typing or runtime claim follows.
-/
set_option autoImplicit false
namespace Effect4.Codegen
open TypeScript Effect4.Program Template Templates
variable {Op : Type} {classes : Classes.Classes} {sig : Signature Op}
  {spell : String → List RowArg → Option Op} {ann : List Nat → Option (List Ty)}
  {root : Eff Op} {env0 : TyEnv}

/-- Successful statement printing supplies its actual context at the statement address. -/
theorem site_stmt_context {contexts : List Nat → Option (PrintEliminators.Context Op)}
    {st : Program.Stmt Op} {path : List Nat} {n declared : Nat} {target : TypeScript.Stmt}
    (printed : cata_stmt (typedSitesAlg sig ann contexts) st path n = .ok (target, declared)) :
    ∃ ctx, contexts path = some ctx ∧
      cata_stmt (typedSitesAlg sig ann contexts) st path n = .ok (target, declared) := by
  obtain ⟨ctor, args, viewed⟩ : ∃ ctor args, view .stmt st = (ctor, args) := ⟨_, _, rfl⟩
  have built : build .stmt ctor args = some st := by
    have h := build_view .stmt st
    rwa [viewed] at h
  have equation := typedSites_cata_build sig ann contexts .stmt ctor args st built path
  cases found : contexts path with
  | some ctx => exact ⟨ctx, rfl, printed⟩
  | none =>
    simp only [cataFam] at equation
    rw [equation, found] at printed
    cases printed

/-- The selected statement row keeps the heterogeneous typed captures and declaration count. -/
theorem site_stmtPrint_inv {ctx : PrintEliminators.Context Op}
    {inferred : Option (List Ty)} {ctor : String} {args : List (ArgF Op Carrier)}
    {n declared : Nat} {target : TypeScript.Stmt}
    (printed : PrintEliminators.layer sig ctx inferred .stmt ctor args n = .ok (target, declared)) :
    ∃ row t τ, Templates.table.find? (fun r => r.selects .stmt ctor args) = some row ∧
      row.out = .stmt t ∧
      PrintEliminators.printArgs sig ctx .stmt n (.stmt t) args 0 = .ok τ ∧
      instStmt n τ t = some target ∧ declared = t.declares := by
  unfold PrintEliminators.layer PrintEliminators.need at printed
  aesop

set_option maxHeartbeats 2000000 in
/-- The statement template erases through its actual selected row and source captures.
The complete family theorem supplies only its smaller-target recursive callbacks. -/
theorem eraseSiteStmt_print
    {path : List Nat} {n : Nat} {st : Program.Stmt Op} {s : TypeScript.Stmt} {declared : Nat}
    (hchild : ∀ path fam d (source : EffSelfCarrier Op fam) y,
      sizeOf y < sizeOf s → SiteFocused root sig env0 path fam source d → ReadableAt classes sig fam source d →
      PrintedCaptureAt (typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root)) path d fam source (.expr y) →
      PrintsTo sig d fam source (.expr ((eraseT classes sig spell fam d y).getD y)))
    (hchildren : ∀ path fam d (source : EffSelfCarrier Op fam) ys,
      sizeOf ys < sizeOf s → SiteFocused root sig env0 path fam source d → ReadableAt classes sig fam source d →
      PrintedCaptureAt (typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root)) path d fam source (.exprs ys) →
      PrintsTo sig d fam source (.exprs (eraseSpine classes sig spell fam d ys)))
    (hblock : ∀ path d (source : Stmts Op) ss,
      sizeOf ss < sizeOf s → SiteFocused root sig env0 path .stmts source d → ReadableAt classes sig .stmts source d →
      PrintedCaptureAt (typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root)) path d .stmts source (.stmts ss) →
      PrintsTo sig d .stmts source (.stmts (eraseStmts classes sig spell d ss)))
    (focus : SiteFocused root sig env0 path .stmt st n)
    (printed : cata_stmt (typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root)) st path n = .ok (s, declared))
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
  obtain ⟨ctx, found, _⟩ := site_stmt_context printed
  have hpLayer : PrintEliminators.layer sig ctx (ann path) .stmt ctor
      (atAddress path (args.map (ArgF.fold (typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root)))) 0) n = .ok (s, declared) := by
    have equation := typedSites_cata_build sig ann
      (PrintEliminators.contextAtTable (annotate sig env0 root) root)
      .stmt ctor args st hbuild path
    simp only [cataFam] at equation
    rw [equation, found] at printed
    exact printed
  obtain ⟨d, hd⟩ := readable
  change cata_stmt (readableAlg classes sig) st n = some d at hd
  have hdom : domLayer classes sig .stmt ctor
      (args.map (ArgF.fold (readableAlg classes sig))) n = some d := by
    have h := cata_build (domLayer classes sig) .stmt ctor args st hbuild
    simp only [cataFam] at h
    rw [show readableAlg classes sig = EffAlgebra.ofLayer (domLayer classes sig) from rfl, h] at hd
    exact hd
  obtain ⟨row, t, τ, hfind, hout, hτ, hinst, rfl⟩ := site_stmtPrint_inv hpLayer
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
  have hsortsCtor : argSorts .stmt row.ctor = some (args.map argSortOf) := by
    rw [hctor]
    exact hsorts
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
  have hτrow : PrintEliminators.printArgs sig ctx row.fam n row.out
      (atAddress path (args.map (ArgF.fold (typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root)))) 0) 0 = .ok τ := by
    rw [hfamily, hout]
    exact hτ
  have hrrow : argsReadable classes sig row.fam n row.out (rowDaemon row)
      (args.map (ArgF.fold (readableAlg classes sig))) 0 = true := by
    rw [hfamily, hout]
    exact hr
  have hmatched : ∀ i ∈ row.out.holes, lookup σ i = lookup τ i := by
    intro i hi
    exact hagree i (by rwa [hout] at hi)
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
  have recursive : ∀ i fam source, args[i]? = some (.child fam source) →
      ∀ capture (member : (i, capture) ∈ σ),
      let depth := argDepth row.fam (.child fam) n (row.out.levelAt i)
      ReadableAt classes sig fam source depth →
      PrintedCaptureAt (typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root)) (path ++ [(args.take i).countP isChildArg]) depth fam source capture →
      PrintsTo sig depth fam source
        (eraseCapture row (args.map argSortOf) n σ child' children' block' ⟨(i, capture), member⟩) := by
    intro i fam source hsource capture member depth hread htyped
    obtain ⟨childCtx, childFound⟩ := printedCaptureAt_context htyped
    have childFocus := siteFocused_child focus hview hfindSource hsource childFound
      (fun _ refused => nomatch hout.symm.trans refused)
    rw [← hfamily] at childFocus
    have hslot : (args.map argSortOf)[i]? = some (.child fam) := by
      simp only [List.getElem?_map, hsource, Option.map_some, argSortOf]
    cases capture with
    | expr y =>
      simpa only [eraseCapture, hslot, Option.getD_some, child'] using
        hchild _ fam depth source y (matchStmt_below n t s σ hσ (i, .expr y) member) childFocus hread htyped
    | exprs ys =>
      simpa only [eraseCapture, hslot, Option.getD_some, children'] using
        hchildren _ fam depth source ys (matchStmt_below n t s σ hσ (i, .exprs ys) member) childFocus hread htyped
    | stmts ss =>
      have hfam : fam = .stmts := by
        cases fam <;> simp only [PrintedCaptureAt] at htyped ⊢
      subst fam
      simpa only [eraseCapture, hslot, Option.getD_some, block'] using
        hblock _ depth source ss (matchStmt_below n t s σ hσ (i, .stmts ss) member) childFocus hread htyped
    | _ => cases fam <;> cases htyped
  have hτplainRow : printArgs sig row.fam n row.out
      (args.map (ArgF.fold (printAlg sig))) 0 = .ok τplain := by
    rw [hfamily, hout]
    exact hτplain
  have erasedAgree := eraseCaptures_siteArgs sig ctx row (args.map argSortOf) n σ
    child' children' block'
    (atAddress path (args.map (ArgF.fold (typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root)))) 0)
    (args.map (ArgF.fold (printAlg sig))) τ τplain
    (by simp only [length_atAddress, List.length_map]) hτrow hτplainRow hmatched
    (fun i hi => holesStmt_of_instStmt n τ t s hinst i (by rwa [hout] at hi))
    (fun i ta pa capture member _ typedAt plainAt typedPrint =>
      source_site_slot_transport classes sig (typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root)) path ctx row n args σ
        child' children' block' hrrow recursive i ta pa capture member typedAt plainAt typedPrint)
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
Placement: exact-codecs, R8, statement-spine step of typed-site print erasure.
Consumer: the full source-image erasure theorem.
The source address, readable fragment and actual successful typed print remain explicit.
The existing reader law identifies the declaration count; actual child contexts supply environments.
This proves syntax reconstruction. It establishes no TypeScript typing or runtime property.
-/
set_option autoImplicit false
namespace Effect4.Codegen
open TypeScript Effect4.Program Template Templates
variable {Op : Type} {classes : Classes.Classes} {sig : Signature Op}
  {spell : String → List RowArg → Option Op} {ann : List Nat → Option (List Ty)}
  {root : Eff Op} {env0 : TyEnv}

/-- The statement templates declare exactly the source binder count. -/
theorem table_stmt_declarations : Templates.table.all (fun row =>
    match row.fam, row.out with
    | .stmt, .stmt tpl => decide (tpl.declares = if row.ctor = "bindYield" then 1 else 0)
    | _, _ => true) = true := by decide

/-- Ordinary statement printing reports the binder count of the source statement. -/
theorem print_stmt_binder_count {st : Program.Stmt Op} {tail : Stmts Op}
    {n d : Nat} {target : TypeScript.Stmt}
    (printed : cata_stmt (printAlg sig) st n = .ok (target,d)) :
    (Node.stmts (.cons st tail)).binders 1 = d := by
  obtain ⟨ctor, args, viewed⟩ : ∃ ctor args, view .stmt st = (ctor,args) := ⟨_,_,rfl⟩
  have built : build .stmt ctor args = some st := by
    have h := build_view .stmt st
    rwa [viewed] at h
  have equation := cata_build (tableLayer sig) .stmt ctor args st built
  simp only [cataFam] at equation
  rw [show printAlg sig = EffAlgebra.ofLayer (tableLayer sig) from rfl, equation] at printed
  obtain ⟨row, tpl, subst, selected, output, _, _, rfl⟩ := stmtPrint_inv printed
  have selectSource : Templates.table.find? (fun r => r.selects .stmt ctor args) = some row := by
    simpa only [selects_fold] using selected
  have selectedSource := List.find?_some selectSource
  obtain ⟨family, constructor⟩ := selects_fam_ctor selectedSource
  have metadata := List.all_eq_true.mp table_stmt_declarations row
    (List.mem_of_find?_eq_some selectSource)
  simp only [family, output] at metadata
  have declared : tpl.declares = if ctor = "bindYield" then 1 else 0 := by
    rw [constructor] at metadata
    exact of_decide_eq_true metadata
  rw [declared]
  cases st <;> cases viewed <;> rfl

/-- The head of a statement spine receives the parent's actual environment. -/
theorem siteFocused_stmts_head {path : List Nat} {n : Nat} {st : Program.Stmt Op} {tail : Stmts Op}
    (focus : SiteFocused root sig env0 path .stmts (.cons st tail) n) :
    SiteFocused root sig env0 (path ++ [0]) .stmt st n := by
  obtain ⟨sourceAt, rho, envAt, length, _⟩ := focus
  refine ⟨Node.at_child sourceAt rfl, .body rho.tyEnv rho.inLoop, ?_, length, True.intro⟩
  exact Node.envAt_child sourceAt envAt rfl rfl

/-- The actual tail context extends by precisely the source head's printed declaration count. -/
theorem siteFocused_stmts_tail {path : List Nat} {n d : Nat} {st : Program.Stmt Op} {tail : Stmts Op}
    {target : TypeScript.Stmt} {ctx : PrintEliminators.Context Op}
    (focus : SiteFocused root sig env0 path .stmts (.cons st tail) n)
    (printed : cata_stmt (printAlg sig) st n = .ok (target,d))
    (found : PrintEliminators.contextAtTable (annotate sig env0 root) root (path ++ [1]) = some ctx) :
    SiteFocused root sig env0 (path ++ [1]) .stmts tail (n+d) := by
  obtain ⟨sourceAt, parent, parentAt, parentLength, _⟩ := focus
  obtain ⟨_, rho, rhoAt, _, _, _⟩ := PrintEliminators.contextAtTable_annotate_facts found
  have step : (Node.stmts (.cons st tail)).child 1 = some (.stmts tail) := rfl
  have envStep : (Node.stmts (.cons st tail)).childEnv sig parent 1 = some rho := by
    have h := rhoAt
    rw [Node.envAt_append, sourceAt, parentAt] at h
    simpa only [nodeOfFamily, Option.bind_some, Node.envAt, step, Option.bind_fun_some] using h
  have binder := print_stmt_binder_count (tail := tail) printed
  have depth : rho.tyEnv.length = n+d := by
    cases st with
    | bindYield eff =>
      change 1 = d at binder
      subst d
      simp only [Node.childEnv] at envStep
      obtain ⟨ty, _, assembled⟩ := Option.map_eq_some_iff.mp envStep
      cases assembled
      change (parent.tyEnv ++ [ty.answer]).length = n + 1
      rw [List.length_append, List.length_singleton, parentLength]
    | _ =>
      change 0 = d at binder
      subst d
      simp only [Node.childEnv, Option.some.injEq] at envStep
      subst rho
      exact parentLength.trans (Nat.add_zero n).symm
  exact ⟨Node.at_child sourceAt step, rho, rhoAt, depth, True.intro⟩

/-- The site context gates the generated spine; successful printing retains the ordinary tail depth. -/
theorem typedSites_stmts_cons {contexts : List Nat → Option (PrintEliminators.Context Op)}
    (st : Program.Stmt Op) (ss : Stmts Op) (path : List Nat) (n : Nat)
    {ctx : PrintEliminators.Context Op} (found : contexts path = some ctx) :
    cata_stmts (typedSitesAlg sig ann contexts) (.cons st ss) path n =
      (cata_stmt (typedSitesAlg sig ann contexts) st (path ++ [0]) n).bind fun head =>
        (cata_stmts (typedSitesAlg sig ann contexts) ss (path ++ [1]) (n+head.2)).bind fun tail =>
          .ok (head.1 :: tail) := by
  have equation := typedSites_cata_build sig ann contexts .stmts "cons"
    [.child .stmt st, .child .stmts ss] (.cons st ss) rfl path
  simp only [cataFam] at equation
  rw [equation, found]
  rfl

/-- Reconstruct the statement spine from its selected statement row and its smaller tail. -/
theorem eraseSiteStmts_print_step (hl : LawfulSpelling sig spell) {m : Nat}
    (hstmt : ∀ path n (st : Program.Stmt Op) (s : TypeScript.Stmt) (declared : Nat),
      sizeOf s < m → SiteFocused root sig env0 path .stmt st n → ReadableAt classes sig .stmt st n →
      cata_stmt (typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root)) st path n = .ok (s, declared) →
      ∃ plain,
        (Templates.table.findSome? fun row => eraseStmtRow n s row
          (fun fam d y _ => (eraseT classes sig spell fam d y).getD y)
          (fun fam d ys _ => eraseSpine classes sig spell fam d ys)
          (fun d body _ => eraseStmts classes sig spell d body)) = some (plain, declared) ∧
        cata_stmt (printAlg sig) st n = .ok (plain, declared))
    (htail : ∀ path n (ss : Stmts Op) (tail : List TypeScript.Stmt), sizeOf tail < m →
      SiteFocused root sig env0 path .stmts ss n → ReadableAt classes sig .stmts ss n →
      PrintedCaptureAt (typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root)) path n .stmts ss (.stmts tail) →
      PrintsTo sig n .stmts ss (.stmts (eraseStmts classes sig spell n tail))) :
    ∀ path n (ss : Stmts Op) (target : List TypeScript.Stmt), sizeOf target ≤ m →
      SiteFocused root sig env0 path .stmts ss n → ReadableAt classes sig .stmts ss n →
      PrintedCaptureAt (typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root)) path n .stmts ss (.stmts target) →
      PrintsTo sig n .stmts ss (.stmts (eraseStmts classes sig spell n target))
  | path, n, ss, target, hx, focus, hr, hp => by
    obtain ⟨ctx, found⟩ := printedCaptureAt_context hp
    cases ss with
    | nil =>
      have equation := typedSites_cata_build sig ann
        (PrintEliminators.contextAtTable (annotate sig env0 root) root)
        .stmts "nil" [] .nil rfl path
      simp only [cataFam] at equation
      simp only [PrintedCaptureAt] at hp
      rw [equation, found] at hp
      cases hp
      rw [eraseStmts]
      rfl
    | cons st ss =>
      simp only [PrintedCaptureAt, typedSites_stmts_cons st ss path n found] at hp
      obtain ⟨⟨s, declared⟩, hs, hp⟩ := bind_eq_ok.mp hp
      obtain ⟨tail, htailPrinted, htarget⟩ := bind_eq_ok.mp hp
      cases htarget
      change sizeOf (s::tail) ≤ m at hx
      obtain ⟨d, hd⟩ := hr
      simp only [cataFam, dom_stmts_cons, Option.bind_eq_some_iff] at hd
      obtain ⟨d1, hd1, d2, hd2, _⟩ := hd
      have hsize : sizeOf (s::tail) = 1 + sizeOf s + sizeOf tail := List.cons.sizeOf_spec s tail
      obtain ⟨plain, hrow, hplain⟩ := hstmt (path++[0]) n st s declared (by omega)
        (siteFocused_stmts_head focus) ⟨d1,hd1⟩ hs
      have hdecl : d1 = declared :=
        (readStmt_print (classes := classes) (sig := sig) (spell := spell)
          (m := sizeOf plain) (fun smaller _ => printsBackUpTo hl smaller)
          (Nat.le_refl _) hplain hd1).2
      subst d1
      have tailPrinted : PrintedCaptureAt
          (typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root))
          (path++[1]) (n+declared) .stmts ss (.stmts tail) := htailPrinted
      obtain ⟨tailCtx, tailFound⟩ := printedCaptureAt_context tailPrinted
      have tailFocus := siteFocused_stmts_tail focus hplain tailFound
      have htailPlain := htail (path++[1]) (n+declared) ss tail (by omega) tailFocus ⟨d2,hd2⟩ tailPrinted
      simp only [PrintsTo] at htailPlain ⊢
      rw [eraseStmts, hrow]
      simp only [cata_stmts_cons, hplain, htailPlain, ok_bind]
      rfl

end Effect4.Codegen

namespace Effect4.Codegen.EraseTermTypes
open TypeScript

-- Placement: exact-codecs R8, successful typed-print erasure.
-- Consumer: decorator template normalization in the P2b family node step.
-- These laws erase only the node header; their arbitrary children remain untouched.

theorem eraseNode_option (n : Nat) (a lA lE lR rA rE rR : TypeRef)
    (input left right : Expr) :
    eraseNode n (.call (.generic (.ident "optionCase") [a,lA,lE,lR,rA,rE,rR])
      [input, .arrow none left, .lambda (Template.params n [0]) right none]) =
    .call (.ident "optionCase")
      [input, .arrow none left, .lambda (Template.params n [0]) right none] := by
  simp only [eraseNode, decide_true, ↓reduceIte]

theorem eraseNode_tag (n : Nat) (source lA lE lR rA rE rR : TypeRef)
    (tag : String) (input left right : Expr) :
    eraseNode n (.call (.generic (.ident "caseTag") [source,.literal tag,lA,lE,lR,rA,rE,rR])
      [input, .str tag, .lambda (Template.params n [0]) left none,
        .lambda (Template.params n [0]) right none]) =
    .call (.ident "caseTag") [input, .str tag, .lambda (Template.params n [0]) left none,
      .lambda (Template.params n [0]) right none] := by
  have head : ["caseTag", "caseTagR"].contains "caseTag" = true := by decide
  simp only [eraseNode, decide_true, head, Bool.true_and, ↓reduceIte]

theorem eraseNode_recordTag (n : Nat) (source lA lE lR rA rE rR : TypeRef)
    (tag : String) (input left right : Expr) :
    eraseNode n (.call (.generic (.ident "caseTagR") [source,.literal tag,lA,lE,lR,rA,rE,rR])
      [input, .str tag, .lambda (Template.params n [0]) left none,
        .lambda (Template.params n [0]) right none]) =
    .call (.ident "caseTagR") [input, .str tag, .lambda (Template.params n [0]) left none,
      .lambda (Template.params n [0]) right none] := by
  have head : ["caseTag", "caseTagR"].contains "caseTagR" = true := by decide
  simp only [eraseNode, decide_true, head, Bool.true_and, ↓reduceIte]

theorem eraseNode_fiber (n : Nat) (a e : TypeRef) (input : Expr) (head : String)
    (supported : head = "Fiber.join" ∨ head = "Fiber.await" ∨ head = "Fiber.interrupt") :
    eraseNode n (.call (.generic (.ident head) [a,e]) [input]) =
      .call (.ident head) [input] := by
  rcases supported with rfl | rfl | rfl
  · have head : ["Fiber.join", "Fiber.await", "Fiber.interrupt"].contains "Fiber.join" = true := by decide
    simp only [eraseNode, head, ↓reduceIte]
  · have head : ["Fiber.join", "Fiber.await", "Fiber.interrupt"].contains "Fiber.await" = true := by decide
    simp only [eraseNode, head, ↓reduceIte]
  · have head : ["Fiber.join", "Fiber.await", "Fiber.interrupt"].contains "Fiber.interrupt" = true := by decide
    simp only [eraseNode, head, ↓reduceIte]

theorem eraseNode_closeScope (n : Nat) (a e : TypeRef) (scope exit : Expr) :
    eraseNode n (.call (.generic (.ident "Scope.close") [a,e]) [scope,exit]) =
      .call (.ident "Scope.close") [scope,exit] := by
  have head : ["Fiber.runIn", "Scope.close"].contains "Scope.close" = true := by decide
  simp only [eraseNode, head, ↓reduceIte]

theorem eraseNode_scoped (n : Nat) (a e r : TypeRef) (child : Expr) :
    eraseNode n (.call (.generic (.ident "Effect.scoped") [a,e,r]) [child]) =
      .call (.ident "Effect.scoped") [child] := by simp only [eraseNode]

theorem eraseNode_acquireRelease (n : Nat) (a e r releaseR : TypeRef) (acquire release : Expr) :
    eraseNode n (.call (.generic (.ident "Effect.acquireRelease") [a,e,r,releaseR])
      [acquire,.lambda (Template.params n [0,1]) release none]) =
      .call (.ident "Effect.acquireRelease") [acquire,.lambda (Template.params n [0,1]) release none] := by
  simp only [eraseNode, decide_true, ↓reduceIte]

theorem eraseNode_forkIn (n : Nat) (a e r : TypeRef) (child scope options : Expr) :
    eraseNode n (.call (.generic (.ident "Effect.forkIn") [a,e,r]) [child,scope,options]) =
      .call (.ident "Effect.forkIn") [child,scope,options] := by simp only [eraseNode]

theorem eraseNode_one_two (n : Nat) (ty : TypeRef) (child options : Expr) (head : String)
    (supported : head = "Effect.forkChild" ∨ head = "Effect.forkDetach" ∨
      head = "Effect.forkScoped" ∨ head = "Fiber.interruptAllAs") :
    eraseNode n (.call (.generic (.ident head) [ty]) [child,options]) =
      .call (.ident head) [child,options] := by
  rcases supported with rfl | rfl | rfl | rfl <;> rfl

theorem eraseNode_one_one (n : Nat) (ty : TypeRef) (input : Expr) (head : String)
    (supported : head = "Fiber.interruptAll" ∨ head = "Fiber.awaitAll") :
    eraseNode n (.call (.generic (.ident head) [ty]) [input]) =
      .call (.ident head) [input] := by
  rcases supported with rfl | rfl <;> rfl

-- Consumer: first-match template separation after typed header normalization.
-- Every changing branch retains the call constructor at the target root.
theorem eraseNode_nodeLike (n : Nat) (x : Expr) :
    Effect4.Codegen.Template.nodeLike (eraseNode n x) = Effect4.Codegen.Template.nodeLike x := by
  fun_cases eraseNode n x <;> rfl

-- The canonical outputs have bare roots; a second header pass changes nothing.
-- Consumer: eraseT_normalize_root, then transparent withFiber lower-family recursion.
-- Placement: exact-codecs R8; consumer: eraseNode_idempotent.
private theorem bare_not_runIn (n : Nat) (name : String) (args : List Expr)
    (other : name ≠ "Effect.withFiber") :
    eraseNode n (.call (.ident name) args) = .call (.ident name) args :=
  Effect4.Codegen.eraseNode_of_exprHead_except_runIn n _ rfl other

-- A selected finite list excludes the wrapper head by a concrete Boolean witness.
-- No variable String equality or Boolean reflexivity is simplified.
private theorem selected_bare (n : Nat) (names : List String) (name : String)
    (args : List Expr) (selected : names.contains name = true)
    (excluded : names.contains "Effect.withFiber" = false) :
    eraseNode n (.call (.ident name) args) = .call (.ident name) args := by
  apply bare_not_runIn n name args
  intro equal
  subst name
  rw [excluded] at selected
  cases selected

theorem eraseNode_idempotent (n : Nat) (x : Expr) :
    eraseNode n (eraseNode n x) = eraseNode n x := by
  fun_cases eraseNode n x
  case case1 => exact Effect4.Codegen.eraseNode_rawRunIn n _ _
  case case2 => exact bare_not_runIn n "optionCase" _ (by decide)
  case case3 h => simp only [eraseNode, if_neg h]
  case case4 name _ _ _ _ _ _ _ _ _ _ _ _ _ _ h =>
    apply selected_bare n ["caseTag", "caseTagR"] name _ _ (by decide)
    simp only [Bool.and_eq_true] at h
    exact h.1.1.1
  case case5 h => simp only [eraseNode, if_neg h]
  case case6 name _ _ _ h =>
    exact selected_bare n ["Fiber.join", "Fiber.await", "Fiber.interrupt"] name _ h (by decide)
  case case7 h => simp only [eraseNode, if_neg h]
  case case8 name _ _ _ _ h =>
    exact selected_bare n ["Fiber.runIn", "Scope.close"] name _ h (by decide)
  case case9 h => simp only [eraseNode, if_neg h]
  case case10 => exact bare_not_runIn n "Effect.scoped" _ (by decide)
  case case11 => exact bare_not_runIn n "Effect.acquireRelease" _ (by decide)
  case case12 h => simp only [eraseNode, if_neg h]
  case case13 => exact bare_not_runIn n "Effect.forkIn" _ (by decide)
  case case14 name _ _ _ h =>
    exact selected_bare n ["Effect.forkChild", "Effect.forkDetach", "Effect.forkScoped", "Fiber.interruptAllAs"] name _ h (by decide)
  case case15 h => simp only [eraseNode, if_neg h]
  case case16 name _ _ h =>
    exact selected_bare n ["Fiber.interruptAll", "Fiber.awaitAll"] name _ h (by decide)
  case case17 h => simp only [eraseNode, if_neg h]
  case case18 noRun noOption noTag noFiber noPair noScoped noAcquire noFork noTwo noOne =>
    unfold eraseNode
    split
    · exact False.elim (noRun _ _ _ _ rfl)
    · exact False.elim (noOption _ _ _ _ _ _ _ _ _ _ _ rfl)
    · exact False.elim (noTag _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl)
    · exact False.elim (noFiber _ _ _ _ rfl)
    · exact False.elim (noPair _ _ _ _ _ rfl)
    · exact False.elim (noScoped _ _ _ _ rfl)
    · exact False.elim (noAcquire _ _ _ _ _ _ _ rfl)
    · exact False.elim (noFork _ _ _ _ _ _ rfl)
    · exact False.elim (noTwo _ _ _ _ rfl)
    · exact False.elim (noOne _ _ _ rfl)
    · rfl

end Effect4.Codegen.EraseTermTypes

namespace Effect4.Codegen
open TypeScript Effect4.Program
variable {Op : Type}

-- Placement: exact-codecs R8, successful typed-print erasure.
-- Consumer: transparent eff.withFiber, using the IH on original typed action syntax.
-- No source, typing, spelling, or whole-erasure premise is introduced here.
theorem eraseT_normalize_root (classes : Classes.Classes) (sig : Signature Op)
    (spell : String → List RowArg → Option Op) (fam : EffFam) (n : Nat) (x : Expr) :
    eraseT classes sig spell fam n (EraseTermTypes.eraseNode n x) =
      eraseT classes sig spell fam n x := by
  conv =>
    lhs
    rw [eraseT]
    rw [EraseTermTypes.eraseNode_idempotent]
  conv =>
    rhs
    rw [eraseT]

end Effect4.Codegen


set_option autoImplicit false
namespace Effect4.Codegen
open TypeScript Effect4.Program Template Templates
variable {Op : Type} {classes : Classes.Classes} {sig : Signature Op}
  {spell : String → List RowArg → Option Op} {root : Eff Op} {env0 : TyEnv}
  {ann : List Nat → Option (List Ty)}

set_option maxHeartbeats 3000000 in
/-- A normalized rigid site reconstructs the ordinary row at its actual source address.
Placement: exact-codecs R8; consumer: the expression clause of SitesEraseUpTo.
Normalization is the finite local decorate inverse, not a whole-print certificate. -/
theorem eraseT_site_rigid_step {fam : EffFam} {path : List Nat} {n : Nat}
    {source : EffSelfCarrier Op fam} {ctor : String} {args : List (ArgF Op (EffSelfCarrier Op))}
    {row : Templates.Row} {t : Tpl} {τ τplain : Subst} {ctx : PrintEliminators.Context Op}
    {x y plain : Expr} {k : Nat}
    (family : fam = .eff ∨ fam = .action ∨ fam = .layer)
    (focus : SiteFocused root sig env0 path fam source n)
    (viewed : view fam source = (ctor, args))
    (selected : Templates.table.find? (fun row => row.selects fam ctor args) = some row)
    (index : Templates.table[k]? = some row)
    (sorts : argSorts row.fam row.ctor = some (args.map argSortOf))
    (output : row.out = .tpl t) (rigid : t.rigid = true)
    (printed : PrintEliminators.printArgs sig ctx row.fam n row.out
      (atAddress path (args.map (ArgF.fold (typedSitesAlg sig ann
        (PrintEliminators.contextAtTable (annotate sig env0 root) root)))) 0) 0 = .ok τ)
    (instantiated : inst n τ t = some y)
    (normalized : EraseTermTypes.eraseNode n x = y)
    (readable : argsReadable classes sig row.fam n row.out (rowDaemon row)
      (args.map (ArgF.fold (readableAlg classes sig))) 0 = true)
    (ordinaryArgs : printArgs sig row.fam n row.out (args.map (ArgF.fold (printAlg sig))) 0 = .ok τplain)
    (ordinaryInst : inst n τplain t = some plain)
    (hchild : ∀ path fam d (child : EffSelfCarrier Op fam) value,
      sizeOf value < sizeOf x → SiteFocused root sig env0 path fam child d →
      ReadableAt classes sig fam child d →
      PrintedCaptureAt (typedSitesAlg sig ann
        (PrintEliminators.contextAtTable (annotate sig env0 root) root)) path d fam child (.expr value) →
      (∃ plain, eraseT classes sig spell fam d value = some plain ∧ PrintsTo sig d fam child (.expr plain)) ∧
        nodeLike (EraseTermTypes.eraseNode d value) = true)
    (hchildren : ∀ path fam d (child : EffSelfCarrier Op fam) values,
      sizeOf values < sizeOf x → SiteFocused root sig env0 path fam child d →
      ReadableAt classes sig fam child d →
      PrintedCaptureAt (typedSitesAlg sig ann
        (PrintEliminators.contextAtTable (annotate sig env0 root) root)) path d fam child (.exprs values) →
      PrintsTo sig d fam child (.exprs (eraseSpine classes sig spell fam d values)))
    (hblock : ∀ path d (child : Stmts Op) values,
      sizeOf values < sizeOf x → SiteFocused root sig env0 path .stmts child d →
      ReadableAt classes sig .stmts child d →
      PrintedCaptureAt (typedSitesAlg sig ann
        (PrintEliminators.contextAtTable (annotate sig env0 root) root)) path d .stmts child (.stmts values) →
      PrintsTo sig d .stmts child (.stmts (eraseStmts classes sig spell d values))) :
    eraseT classes sig spell fam n x = some plain ∧ nodeLike y = true := by
  let alg := typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root)
  have selector := List.find?_some selected
  obtain ⟨familyRow, constructor⟩ := selects_fam_ctor selector
  have member := List.mem_of_getElem? index
  have bound : sizeOf y ≤ sizeOf x := by
    rw [← normalized]
    exact eraseNode_size n x
  have childFocus : ∀ i fam d (child : EffSelfCarrier Op fam) capture,
      args[i]? = some (.child fam child) →
      d = argDepth row.fam (.child fam) n (row.out.levelAt i) →
      PrintedCaptureAt alg (path ++ [(args.take i).countP isChildArg]) d fam child capture →
      SiteFocused root sig env0 (path ++ [(args.take i).countP isChildArg]) fam child d := by
    intro i fam d child capture sourceAt depth hp
    obtain ⟨childCtx, found⟩ := printedCaptureAt_context hp
    rw [depth, familyRow]
    exact siteFocused_child focus viewed selected sourceAt found
      (fun _ refused => nomatch output.symm.trans refused)
  have childPrint : ∀ i fam d (child : EffSelfCarrier Op fam) value,
      args[i]? = some (.child fam child) →
      d = argDepth row.fam (.child fam) n (row.out.levelAt i) →
      sizeOf value < sizeOf y → ReadableAt classes sig fam child d →
      PrintedCaptureAt alg (path ++ [(args.take i).countP isChildArg]) d fam child (.expr value) →
      PrintsTo sig d fam child (.expr ((eraseT classes sig spell fam d value).getD value)) := by
    intro i fam d child value sourceAt depth smaller hr hp
    obtain ⟨plain, erased, printed⟩ := (hchild _ fam d child value (by omega)
      (childFocus i fam d child _ sourceAt depth hp) hr hp).1
    rw [erased, Option.getD_some]
    exact printed
  have nodeChildren := site_child_at_hole alg ctx output familyRow rigid
    (by rw [familyRow, output] at printed; exact printed) instantiated
    (by rw [familyRow, output] at readable; exact readable)
    (fun i fam d child value sourceAt depth smaller hr hp => by
      have shape := (hchild _ fam d child value (by omega)
        (childFocus i fam d child _ sourceAt depth hp) hr hp).2
      rwa [EraseTermTypes.eraseNode_nodeLike] at shape)
  have atRow := eraseExprRow_site_rigid alg ctx member selector sorts output rigid printed
    instantiated readable ordinaryArgs ordinaryInst childPrint
    (fun i fam d child values sourceAt depth smaller hr hp =>
      hchildren _ fam d child values (by omega) (childFocus i fam d child _ sourceAt depth hp) hr hp)
    (fun i d child values sourceAt depth smaller hr hp =>
      hblock _ d child values (by omega) (childFocus i .stmts d child _ sourceAt depth hp) hr hp)
  have selectedErased : eraseT classes sig spell fam n y = some plain := by
    apply eraseT_of_row (by rw [← normalized]; exact EraseTermTypes.eraseNode_idempotent n x) index
      (fun j earlier rj atIndex => ?_) atRow
    rcases apart_of_lt atIndex index earlier with different | apart
    · exact eraseExprRow_none_of_fam (by rwa [familyRow] at different)
    · exact erase_earlier_none_rigid apart output rigid sorts instantiated nodeChildren
  have erased : eraseT classes sig spell fam n x = some plain := by
    rw [← eraseT_normalize_root classes sig spell fam n x, normalized]
    exact selectedErased
  have shape := table_fact table_shape member
  have top : t.nodeTop = true := by
    rcases family with rfl | rfl | rfl <;>
      simpa only [rowShape, familyRow, output, rigid, ↓reduceIte] using shape
  exact ⟨erased, inst_nodeLike n τ t y top instantiated⟩

end Effect4.Codegen

set_option autoImplicit false
namespace Effect4.Codegen
open TypeScript Effect4.Program Template Templates
variable {Op : Type} {classes : Classes.Classes} {sig : Signature Op}
  {spell : String → List RowArg → Option Op} {ann : List Nat → Option (List Ty)}
  {root : Eff Op} {env0 : TyEnv}

/-- A focused node's child whose context the table records is focused at the child's scope.
Placement: exact-codecs R8; consumer: the expression spine steps below. Inside an invocation's
programs a spine child takes its environment from its parameter, so only the recorded context,
not the parent's, fixes it (decisions row 340). -/
theorem siteFocused_found {path : List Nat} {fam : EffFam} {source : EffSelfCarrier Op fam}
    {n i d : Nat} {childFam : EffFam} {child : EffSelfCarrier Op childFam}
    {ctx : PrintEliminators.Context Op}
    (focus : SiteFocused root sig env0 path fam source n)
    (step : (nodeOfFamily fam source).child i = some (nodeOfFamily childFam child))
    (found : PrintEliminators.contextAtTable (annotate sig env0 root) root (path ++ [i]) = some ctx)
    (depth : PrintEliminators.childScope n (nodeOfFamily fam source) i = d)
    (closed : ClosedSiteLevel childFam d) :
    SiteFocused root sig env0 (path ++ [i]) childFam child d := by
  obtain ⟨sourceAt, parent, parentAt, parentLength, _⟩ := focus
  obtain ⟨_, rho, rhoAt, _, _, _⟩ := PrintEliminators.contextAtTable_annotate_facts found
  have envStep : (nodeOfFamily fam source).childEnv sig parent i = some rho := by
    rw [Node.envAt_append, sourceAt, parentAt] at rhoAt
    simp only [Option.bind_some, Node.envAt, step] at rhoAt
    cases environment : (nodeOfFamily fam source).childEnv sig parent i with
    | none => rw [environment] at rhoAt; cases rhoAt
    | some rho' => simpa only [environment, Option.bind_some] using rhoAt
  refine ⟨Node.at_child sourceAt step, rho, rhoAt, ?_, closed⟩
  rw [PrintEliminators.childEnv_length sig parent _ i envStep, parentLength, depth]

/-- The expression spine's head is focused at its parent's depth.
Placement: exact-codecs R8; consumer: typed-site expression spine reconstruction. -/
theorem siteFocused_effs_head {path : List Nat} {n : Nat} {head : Eff Op} {tail : Effs Op}
    {ctx : PrintEliminators.Context Op}
    (focus : SiteFocused root sig env0 path .effs (.cons head tail) n)
    (found : PrintEliminators.contextAtTable (annotate sig env0 root) root (path ++ [0]) = some ctx) :
    SiteFocused root sig env0 (path ++ [0]) .eff head n :=
  siteFocused_found focus rfl found rfl True.intro

theorem siteFocused_effs_tail {path : List Nat} {n : Nat} {head : Eff Op} {tail : Effs Op}
    {ctx : PrintEliminators.Context Op}
    (focus : SiteFocused root sig env0 path .effs (.cons head tail) n)
    (found : PrintEliminators.contextAtTable (annotate sig env0 root) root (path ++ [1]) = some ctx) :
    SiteFocused root sig env0 (path ++ [1]) .effs tail n :=
  siteFocused_found focus rfl found rfl True.intro

/-- The layer spine and both children use the empty environment.
Placement: exact-codecs R8; consumer: typed-site layer spine reconstruction. -/
theorem siteFocused_layers_head {path : List Nat} {n : Nat}
    {head : LayerTerm Op} {tail : LayerTerms Op}
    (focus : SiteFocused root sig env0 path .layers (.cons head tail) n) :
    SiteFocused root sig env0 (path ++ [0]) .layer head n := by
  obtain ⟨sourceAt, parent, envAt, _, closed⟩ := focus
  change n = 0 at closed
  rw [closed]
  exact ⟨Node.at_child sourceAt rfl, .closed,
    Node.envAt_child sourceAt envAt rfl rfl, rfl, rfl⟩

theorem siteFocused_layers_tail {path : List Nat} {n : Nat}
    {head : LayerTerm Op} {tail : LayerTerms Op}
    (focus : SiteFocused root sig env0 path .layers (.cons head tail) n) :
    SiteFocused root sig env0 (path ++ [1]) .layers tail n := by
  obtain ⟨sourceAt, parent, envAt, _, closed⟩ := focus
  change n = 0 at closed
  rw [closed]
  exact ⟨Node.at_child sourceAt rfl, .closed,
    Node.envAt_child sourceAt envAt rfl rfl, rfl, rfl⟩

theorem typedSites_effs_cons {contexts : List Nat → Option (PrintEliminators.Context Op)}
    (head : Eff Op) (tail : Effs Op) (path : List Nat) (n : Nat)
    {ctx : PrintEliminators.Context Op} (found : contexts path = some ctx) :
    cata_effs (typedSitesAlg sig ann contexts) (.cons head tail) path n =
      (cata_eff (typedSitesAlg sig ann contexts) head (path ++ [0]) n).bind fun y =>
        (cata_effs (typedSitesAlg sig ann contexts) tail (path ++ [1]) n).bind fun ys => .ok (y :: ys) := by
  have equation := typedSites_cata_build sig ann contexts .effs "cons"
    [.child .eff head, .child .effs tail] (.cons head tail) rfl path
  simp only [cataFam] at equation
  rw [equation, found]
  rfl

theorem typedSites_layers_cons {contexts : List Nat → Option (PrintEliminators.Context Op)}
    (head : LayerTerm Op) (tail : LayerTerms Op) (path : List Nat) (n : Nat)
    {ctx : PrintEliminators.Context Op} (found : contexts path = some ctx) :
    cata_layers (typedSitesAlg sig ann contexts) (.cons head tail) path n =
      (cata_layer (typedSitesAlg sig ann contexts) head (path ++ [0]) n).bind fun y =>
        (cata_layers (typedSitesAlg sig ann contexts) tail (path ++ [1]) n).bind fun ys => .ok (y :: ys) := by
  have equation := typedSites_cata_build sig ann contexts .layers "cons"
    [.child .layer head, .child .layers tail] (.cons head tail) rfl path
  simp only [cataFam] at equation
  rw [equation, found]
  rfl

theorem eraseSiteSpine_print_step {m : Nat}
    (hexpr : ∀ fam path n (e : EffSelfCarrier Op fam) (y : Expr), sizeOf y < m → SiteFocused root sig env0 path fam e n →
      ReadableAt classes sig fam e n → PrintedCaptureAt (typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root)) path n fam e (.expr y) →
      ∃ plain, eraseT classes sig spell fam n y = some plain ∧ PrintsTo sig n fam e (.expr plain))
    (hlist : ∀ fam path n (e : EffSelfCarrier Op fam) (ys : List Expr), sizeOf ys < m → SiteFocused root sig env0 path fam e n →
      ReadableAt classes sig fam e n → PrintedCaptureAt (typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root)) path n fam e (.exprs ys) →
      PrintsTo sig n fam e (.exprs (eraseSpine classes sig spell fam n ys))) :
    ∀ fam path n (e : EffSelfCarrier Op fam) (xs : List Expr), sizeOf xs ≤ m → SiteFocused root sig env0 path fam e n →
      ReadableAt classes sig fam e n → PrintedCaptureAt (typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root)) path n fam e (.exprs xs) →
      PrintsTo sig n fam e (.exprs (eraseSpine classes sig spell fam n xs))
  | .effs, path, n, e, xs, hx, focus, hr, hp => by
    obtain ⟨ctx, found⟩ := printedCaptureAt_context hp
    cases e with
    | nil =>
      simp only [PrintedCaptureAt] at hp
      have equation := typedSites_cata_build sig ann
        (PrintEliminators.contextAtTable (annotate sig env0 root) root) .effs "nil" [] .nil rfl path
      simp only [cataFam] at equation
      rw [equation, found] at hp
      change (Except.ok ([] : List Expr) : Except PrintRefusal (List Expr)) = .ok xs at hp
      cases hp
      rw [eraseSpine]
      rfl
    | cons e es =>
      simp only [PrintedCaptureAt] at hp
      rw [typedSites_effs_cons e es path n found] at hp
      obtain ⟨y, hy, hp⟩ := bind_eq_ok.mp hp
      obtain ⟨rest, hrest, hxs⟩ := bind_eq_ok.mp hp
      cases hxs
      obtain ⟨d, hd⟩ := hr
      simp only [cataFam, dom_effs_cons, Option.bind_eq_some_iff] at hd
      obtain ⟨d1, hd1, d2, hd2, _⟩ := hd
      have hsz : sizeOf (y :: rest) = 1 + sizeOf y + sizeOf rest := List.cons.sizeOf_spec y rest
      obtain ⟨_, headFound⟩ := printedCaptureAt_context (fam := .eff) (source := e) (capture := .expr y) hy
      obtain ⟨_, tailFound⟩ :=
        printedCaptureAt_context (fam := .effs) (source := es) (capture := .exprs rest) hrest
      obtain ⟨plain, herase, hplain⟩ := hexpr .eff (path ++ [0]) n e y (by omega) (siteFocused_effs_head focus headFound) ⟨d1, hd1⟩ hy
      have htail := hlist .effs (path ++ [1]) n es rest (by omega) (siteFocused_effs_tail focus tailFound) ⟨d2, hd2⟩ hrest
      simp only [PrintsTo] at hplain htail ⊢
      rw [eraseSpine]
      change cata_effs (printAlg sig) (.cons e es) n = .ok
        ((eraseT classes sig spell .eff n y).getD y :: eraseSpine classes sig spell .effs n rest)
      rw [herase]
      simp only [Option.getD_some, cata_effs_cons, hplain, htail, ok_bind]
      rfl
  | .layers, path, n, e, xs, hx, focus, hr, hp => by
    obtain ⟨ctx, found⟩ := printedCaptureAt_context hp
    cases e with
    | nil =>
      simp only [PrintedCaptureAt] at hp
      have equation := typedSites_cata_build sig ann
        (PrintEliminators.contextAtTable (annotate sig env0 root) root) .layers "nil" [] .nil rfl path
      simp only [cataFam] at equation
      rw [equation, found] at hp
      change (Except.ok ([] : List Expr) : Except PrintRefusal (List Expr)) = .ok xs at hp
      cases hp
      rw [eraseSpine]
      rfl
    | cons e es =>
      simp only [PrintedCaptureAt] at hp
      rw [typedSites_layers_cons e es path n found] at hp
      obtain ⟨y, hy, hp⟩ := bind_eq_ok.mp hp
      obtain ⟨rest, hrest, hxs⟩ := bind_eq_ok.mp hp
      cases hxs
      obtain ⟨d, hd⟩ := hr
      simp only [cataFam, dom_layers_cons, Option.bind_eq_some_iff] at hd
      obtain ⟨d1, hd1, d2, hd2, _⟩ := hd
      have hsz : sizeOf (y :: rest) = 1 + sizeOf y + sizeOf rest := List.cons.sizeOf_spec y rest
      obtain ⟨plain, herase, hplain⟩ := hexpr .layer (path ++ [0]) n e y (by omega) (siteFocused_layers_head focus) ⟨d1, hd1⟩ hy
      have htail := hlist .layers (path ++ [1]) n es rest (by omega) (siteFocused_layers_tail focus) ⟨d2, hd2⟩ hrest
      simp only [PrintsTo] at hplain htail ⊢
      rw [eraseSpine]
      change cata_layers (printAlg sig) (.cons e es) n = .ok
        ((eraseT classes sig spell .layer n y).getD y :: eraseSpine classes sig spell .layers n rest)
      rw [herase]
      simp only [Option.getD_some, cata_layers_cons, hplain, htail, ok_bind]
      rfl
  | .eff, _, _, _, _, _, _, _, hp => by simp only [PrintedCaptureAt] at hp
  | .action, _, _, _, _, _, _, _, hp => by simp only [PrintedCaptureAt] at hp
  | .layer, _, _, _, _, _, _, _, hp => by simp only [PrintedCaptureAt] at hp
  | .stmt, _, _, _, _, _, _, _, hp => by simp only [PrintedCaptureAt] at hp
  | .stmts, _, _, _, _, _, _, _, hp => by simp only [PrintedCaptureAt] at hp

end Effect4.Codegen

namespace Effect4.Codegen.EraseTermTypes

open TypeScript

-- Placement: exact-codecs R8, local node inverse of typed-print erasure.
-- Consumer: PrintEliminators.decorate at the actual runIn source template.
theorem eraseNode_runIn (n : Nat) (answer error : TypeRef) (receiver scope : Expr) :
    eraseNode n (.call (.ident "Effect.withFiber")
      [.arrowBlock [] [.exprStmt (.call (.generic (.ident "Fiber.runIn") [answer, error])
        [receiver, scope]), .ret (.ident "Effect.void")] none]) =
    .call (.ident "Effect.withFiber")
      [.arrowBlock [] [.exprStmt (.call (.ident "Fiber.runIn") [receiver, scope]),
        .ret (.ident "Effect.void")] none] := rfl

end Effect4.Codegen.EraseTermTypes

namespace Effect4.Codegen.PrintEliminators
open TypeScript Effect4.Program
variable {Op : Type}

-- Placement: exact-codecs R8, helper of successful typed-print erasure.
-- Consumer: typed template capture reconstruction at the actual source address.
-- This relation names data already computed by annotate; it creates no new refusal.
def ContextMatches (ctx : Context Op) (node : Node Op) (n : Nat) : Prop :=
  ctx.node = node ∧ ctx.env.length = n

-- The bare fixed head needs no recursive child inspection.
theorem eraseNode_bare_call (n : Nat) (head : String) (args : List Expr)
    (other : head ≠ "Effect.withFiber") :
    EraseTermTypes.eraseNode n (.call (.ident head) args) = .call (.ident head) args :=
  Effect4.Codegen.eraseNode_of_exprHead_except_runIn n (.call (.ident head) args) (by rfl) other

-- These node statements retain typed child syntax unchanged.
-- The contextual capture recursion subsequently erases each child exactly once.
-- They do not claim a blanket decorator inverse for transparent eff.withFiber.

set_option maxHeartbeats 250000 in
theorem decorate_awaitFiber_erases (sig : Signature Op) (ctx : Context Op) (n : Nat)
    (receiver : Term) (mode : Effect4.Supervision.ObserverMode) (input : Expr) {out : Expr}
    (actual : ContextMatches ctx (.eff (.awaitFiber receiver mode)) n)
    (printed : decorate sig ctx (.call (.ident (match mode with | .joinEffect => "Fiber.join" | .awaitValue => "Fiber.await")) [input]) = .ok out) :
    EraseTermTypes.eraseNode n out = .call (.ident (match mode with | .joinEffect => "Fiber.join" | .awaitValue => "Fiber.await")) [input] := by
  rcases actual with ⟨node, depth⟩
  cases mode with
  | awaitValue =>
    have bare := eraseNode_bare_call n "Fiber.await" [input] (by decide)
    have typed (a e : TypeRef) := EraseTermTypes.eraseNode_fiber n a e input "Fiber.await"
      (Or.inr (Or.inl rfl))
    aesop (config := {maxRuleApplicationDepth := 100}) (add norm simp
      [decorate, node, need, «columns», withHeadTypes, bind, Except.bind, bare, typed])
  | joinEffect =>
    have bare := eraseNode_bare_call n "Fiber.join" [input] (by decide)
    have typed (a e : TypeRef) := EraseTermTypes.eraseNode_fiber n a e input "Fiber.join"
      (Or.inl rfl)
    aesop (config := {maxRuleApplicationDepth := 100}) (add norm simp
      [decorate, node, need, «columns», withHeadTypes, bind, Except.bind, bare, typed])

set_option maxHeartbeats 250000 in
theorem decorate_scoped_erases (sig : Signature Op) (ctx : Context Op) (n : Nat)
    (child : Eff Op) (input : Expr) {out : Expr}
    (actual : ContextMatches ctx (.eff (.scoped child)) n)
    (printed : decorate sig ctx (.call (.ident "Effect.scoped") [input]) = .ok out) :
    EraseTermTypes.eraseNode n out = .call (.ident "Effect.scoped") [input] := by
  rcases actual with ⟨node, depth⟩
  have bare : EraseTermTypes.eraseNode n (.call (.ident "Effect.scoped") [input]) = (.call (.ident "Effect.scoped") [input]) := by
    exact eraseNode_bare_call n _ _ (by decide)
  aesop (config := {maxRuleApplicationDepth := 100}) (add norm simp [decorate, node, need, «columns», withHeadTypes,
    bind, Except.bind, bare]) (add safe apply [EraseTermTypes.eraseNode_scoped])

set_option maxHeartbeats 250000 in
theorem decorate_acquireRelease_erases (sig : Signature Op) (ctx : Context Op) (n : Nat)
    (acquire release : Eff Op) (first second : Expr) {out : Expr}
    (actual : ContextMatches ctx (.eff (.acquireRelease acquire release)) n)
    (printed : decorate sig ctx (.call (.ident "Effect.acquireRelease") [first,.lambda (Template.params n [0,1]) second none]) = .ok out) :
    EraseTermTypes.eraseNode n out = .call (.ident "Effect.acquireRelease") [first,.lambda (Template.params n [0,1]) second none] := by
  rcases actual with ⟨node, depth⟩
  have bare : EraseTermTypes.eraseNode n (.call (.ident "Effect.acquireRelease") [first,.lambda (Template.params n [0,1]) second none]) = (.call (.ident "Effect.acquireRelease") [first,.lambda (Template.params n [0,1]) second none]) := by
    exact eraseNode_bare_call n _ _ (by decide)
  aesop (config := {maxRuleApplicationDepth := 100}) (add norm simp [decorate, node, need, «columns», withHeadTypes,
    bind, Except.bind, bare]) (add safe apply [EraseTermTypes.eraseNode_acquireRelease])

set_option maxHeartbeats 250000 in
theorem decorate_forkIn_erases (sig : Signature Op) (ctx : Context Op) (n : Nat)
    (child : Eff Op) (options : Effect4.Supervision.ForkOptions) (scope : Term) (first second third : Expr) {out : Expr}
    (actual : ContextMatches ctx (.action (.forkIn child options scope)) n)
    (printed : decorate sig ctx (.call (.ident "Effect.forkIn") [first,third,second]) = .ok out) :
    EraseTermTypes.eraseNode n out = .call (.ident "Effect.forkIn") [first,third,second] := by
  rcases actual with ⟨node, depth⟩
  have bare : EraseTermTypes.eraseNode n (.call (.ident "Effect.forkIn") [first,third,second]) = (.call (.ident "Effect.forkIn") [first,third,second]) := by
    exact eraseNode_bare_call n _ _ (by decide)
  aesop (config := {maxRuleApplicationDepth := 100}) (add norm simp [decorate, node, need, «columns», withHeadTypes,
    bind, Except.bind, bare]) (add safe apply [EraseTermTypes.eraseNode_forkIn])

set_option maxHeartbeats 250000 in
theorem decorate_interrupt_erases (sig : Signature Op) (ctx : Context Op) (n : Nat)
    (receiver : Term) (input : Expr) {out : Expr}
    (actual : ContextMatches ctx (.action (.interrupt receiver)) n)
    (printed : decorate sig ctx (.call (.ident "Fiber.interrupt") [input]) = .ok out) :
    EraseTermTypes.eraseNode n out = .call (.ident "Fiber.interrupt") [input] := by
  rcases actual with ⟨node, depth⟩
  have bare : EraseTermTypes.eraseNode n (.call (.ident "Fiber.interrupt") [input]) = (.call (.ident "Fiber.interrupt") [input]) := by
    exact eraseNode_bare_call n _ _ (by decide)
  have typed (a e : TypeRef) := EraseTermTypes.eraseNode_fiber n a e input "Fiber.interrupt"
    (Or.inr (Or.inr rfl))
  aesop (config := {maxRuleApplicationDepth := 100}) (add norm simp
    [decorate, node, need, «columns», withHeadTypes, bind, Except.bind, bare, typed])

set_option maxHeartbeats 250000 in
theorem decorate_awaitAll_erases (sig : Signature Op) (ctx : Context Op) (n : Nat)
    (receivers : Term) (input : Expr) {out : Expr}
    (actual : ContextMatches ctx (.action (.awaitAll receivers)) n)
    (printed : decorate sig ctx (.call (.ident "Fiber.awaitAll") [input]) = .ok out) :
    EraseTermTypes.eraseNode n out = .call (.ident "Fiber.awaitAll") [input] := by
  rcases actual with ⟨node, depth⟩
  have bare : EraseTermTypes.eraseNode n (.call (.ident "Fiber.awaitAll") [input]) = (.call (.ident "Fiber.awaitAll") [input]) := by
    exact eraseNode_bare_call n _ _ (by decide)
  aesop (config := {maxRuleApplicationDepth := 100}) (add norm simp [decorate, node, need, «columns», withHeadTypes,
    bind, Except.bind, bare]) (add safe apply [EraseTermTypes.eraseNode_one_one])

set_option maxHeartbeats 250000 in
theorem decorate_closeScope_erases (sig : Signature Op) (ctx : Context Op) (n : Nat)
    (scope exit : Term) (first second : Expr) {out : Expr}
    (actual : ContextMatches ctx (.action (.closeScope scope exit)) n)
    (printed : decorate sig ctx (.call (.ident "Scope.close") [first,second]) = .ok out) :
    EraseTermTypes.eraseNode n out = .call (.ident "Scope.close") [first,second] := by
  rcases actual with ⟨node, depth⟩
  have bare : EraseTermTypes.eraseNode n (.call (.ident "Scope.close") [first,second]) = (.call (.ident "Scope.close") [first,second]) := by
    exact eraseNode_bare_call n _ _ (by decide)
  aesop (config := {maxRuleApplicationDepth := 100}) (add norm simp [decorate, node, need, «columns», withHeadTypes,
    bind, Except.bind, bare]) (add safe apply [EraseTermTypes.eraseNode_closeScope])

set_option maxRecDepth 2048 in
set_option maxHeartbeats 250000 in
theorem decorate_option_erases (sig : Signature Op) (ctx : Context Op) (n : Nat)
    (scrutinee : Term) (left right : Eff Op) (input l r : Expr) {out : Expr}
    (actual : ContextMatches ctx (.eff (.select scrutinee .option left right)) n)
    (printed : decorate sig ctx (.call (.ident "optionCase") [input,.arrow none l,.lambda (Template.params n [0]) r none]) = .ok out) :
    EraseTermTypes.eraseNode n out = .call (.ident "optionCase") [input,.arrow none l,.lambda (Template.params n [0]) r none] := by
  rcases actual with ⟨node, depth⟩
  have bare : EraseTermTypes.eraseNode n (.call (.ident "optionCase") [input,.arrow none l,.lambda (Template.params n [0]) r none]) = (.call (.ident "optionCase") [input,.arrow none l,.lambda (Template.params n [0]) r none]) := by
    exact eraseNode_bare_call n _ _ (by decide)
  aesop (config := {maxRuleApplicationDepth := 100}) (add norm simp [decorate, node, depth, need, «columns», withHeadTypes,
    bind, Except.bind, bare]) (add safe apply [EraseTermTypes.eraseNode_option])

set_option maxHeartbeats 250000 in
theorem decorate_tag_erases (sig : Signature Op) (ctx : Context Op) (n : Nat)
    (scrutinee : Term) (tag : String) (left right : Eff Op) (input l r : Expr) {out : Expr}
    (actual : ContextMatches ctx (.eff (.select scrutinee (.tag tag) left right)) n)
    (printed : decorate sig ctx (.call (.ident "caseTag") [input,.str tag,.lambda (Template.params n [0]) l none,.lambda (Template.params n [0]) r none]) = .ok out) :
    EraseTermTypes.eraseNode n out = .call (.ident "caseTag") [input,.str tag,.lambda (Template.params n [0]) l none,.lambda (Template.params n [0]) r none] := by
  rcases actual with ⟨node, depth⟩
  have bare : EraseTermTypes.eraseNode n (.call (.ident "caseTag") [input,.str tag,.lambda (Template.params n [0]) l none,.lambda (Template.params n [0]) r none]) = (.call (.ident "caseTag") [input,.str tag,.lambda (Template.params n [0]) l none,.lambda (Template.params n [0]) r none]) := by
    exact eraseNode_bare_call n _ _ (by decide)
  aesop (config := {maxRuleApplicationDepth := 100}) (add norm simp [decorate, node, depth, need, «columns», withHeadTypes,
    bind, Except.bind, bare]) (add safe apply [EraseTermTypes.eraseNode_tag])

set_option maxHeartbeats 250000 in
theorem decorate_recordTag_erases (sig : Signature Op) (ctx : Context Op) (n : Nat)
    (scrutinee : Term) (tag : String) (left right : Eff Op) (input l r : Expr) {out : Expr}
    (actual : ContextMatches ctx (.eff (.select scrutinee (.recordTag tag) left right)) n)
    (printed : decorate sig ctx (.call (.ident "caseTagR") [input,.str tag,.lambda (Template.params n [0]) l none,.lambda (Template.params n [0]) r none]) = .ok out) :
    EraseTermTypes.eraseNode n out = .call (.ident "caseTagR") [input,.str tag,.lambda (Template.params n [0]) l none,.lambda (Template.params n [0]) r none] := by
  rcases actual with ⟨node, depth⟩
  have bare : EraseTermTypes.eraseNode n (.call (.ident "caseTagR") [input,.str tag,.lambda (Template.params n [0]) l none,.lambda (Template.params n [0]) r none]) = (.call (.ident "caseTagR") [input,.str tag,.lambda (Template.params n [0]) l none,.lambda (Template.params n [0]) r none]) := by
    exact eraseNode_bare_call n _ _ (by decide)
  aesop (config := {maxRuleApplicationDepth := 100}) (add norm simp [decorate, node, depth, need, «columns», withHeadTypes,
    bind, Except.bind, bare]) (add safe apply [EraseTermTypes.eraseNode_recordTag])

set_option maxHeartbeats 250000 in
theorem decorate_fork_erases (sig : Signature Op) (ctx : Context Op) (n : Nat)
    (child : Eff Op) (options : Effect4.Supervision.ForkOptions) (input opts : Expr) {out : Expr}
    (actual : ContextMatches ctx (.action (.fork child options)) n)
    (printed : decorate sig ctx (.call (.ident (if options.daemon then "Effect.forkDetach" else "Effect.forkChild")) [input,opts]) = .ok out) :
    EraseTermTypes.eraseNode n out = .call (.ident (if options.daemon then "Effect.forkDetach" else "Effect.forkChild")) [input,opts] := by
  rcases actual with ⟨node, depth⟩
  have bare : EraseTermTypes.eraseNode n (.call (.ident (if options.daemon then "Effect.forkDetach" else "Effect.forkChild")) [input,opts]) = (.call (.ident (if options.daemon then "Effect.forkDetach" else "Effect.forkChild")) [input,opts]) := by
    cases options.daemon <;> exact eraseNode_bare_call n _ _ (by decide)
  aesop (config := {maxRuleApplicationDepth := 100}) (add norm simp [decorate, node, depth, need, «columns», withHeadTypes,
    bind, Except.bind, bare]) (add safe apply [EraseTermTypes.eraseNode_one_two])

set_option maxHeartbeats 250000 in
theorem decorate_forkScoped_erases (sig : Signature Op) (ctx : Context Op) (n : Nat)
    (child : Eff Op) (options : Effect4.Supervision.ForkOptions) (input opts : Expr) {out : Expr}
    (actual : ContextMatches ctx (.action (.forkScoped child options)) n)
    (printed : decorate sig ctx (.call (.ident "Effect.forkScoped") [input,opts]) = .ok out) :
    EraseTermTypes.eraseNode n out = .call (.ident "Effect.forkScoped") [input,opts] := by
  rcases actual with ⟨node, depth⟩
  have bare : EraseTermTypes.eraseNode n (.call (.ident "Effect.forkScoped") [input,opts]) = (.call (.ident "Effect.forkScoped") [input,opts]) := by
    exact eraseNode_bare_call n _ _ (by decide)
  aesop (config := {maxRuleApplicationDepth := 100}) (add norm simp [decorate, node, depth, need, «columns», withHeadTypes,
    bind, Except.bind, bare]) (add safe apply [EraseTermTypes.eraseNode_one_two])

set_option maxHeartbeats 250000 in
theorem decorate_interruptAll_erases (sig : Signature Op) (ctx : Context Op) (n : Nat)
    (receivers : Term) (input : Expr) {out : Expr}
    (actual : ContextMatches ctx (.action (.interruptAll receivers none)) n)
    (printed : decorate sig ctx (.call (.ident "Fiber.interruptAll") [input]) = .ok out) :
    EraseTermTypes.eraseNode n out = .call (.ident "Fiber.interruptAll") [input] := by
  rcases actual with ⟨node, depth⟩
  have bare : EraseTermTypes.eraseNode n (.call (.ident "Fiber.interruptAll") [input]) = (.call (.ident "Fiber.interruptAll") [input]) := by
    exact eraseNode_bare_call n _ _ (by decide)
  aesop (config := {maxRuleApplicationDepth := 100}) (add norm simp [decorate, node, depth, need, «columns», withHeadTypes,
    bind, Except.bind, bare]) (add safe apply [EraseTermTypes.eraseNode_one_one])

set_option maxHeartbeats 250000 in
theorem decorate_interruptAllAs_erases (sig : Signature Op) (ctx : Context Op) (n : Nat)
    (receivers interruptor : Term) (input who : Expr) {out : Expr}
    (actual : ContextMatches ctx (.action (.interruptAll receivers (some interruptor))) n)
    (printed : decorate sig ctx (.call (.ident "Fiber.interruptAllAs") [input,who]) = .ok out) :
    EraseTermTypes.eraseNode n out = .call (.ident "Fiber.interruptAllAs") [input,who] := by
  rcases actual with ⟨node, depth⟩
  have bare : EraseTermTypes.eraseNode n (.call (.ident "Fiber.interruptAllAs") [input,who]) = (.call (.ident "Fiber.interruptAllAs") [input,who]) := by
    exact eraseNode_bare_call n _ _ (by decide)
  aesop (config := {maxRuleApplicationDepth := 100}) (add norm simp [decorate, node, depth, need, «columns», withHeadTypes,
    bind, Except.bind, bare]) (add safe apply [EraseTermTypes.eraseNode_one_two])

-- Check after the paired nested-runIn inverse and raw P3 helper correction.
set_option maxHeartbeats 250000 in
theorem decorate_runIn_erases (sig : Signature Op) (ctx : Context Op) (n : Nat)
    (receiver scope : Term) (input scopeExpr : Expr) {out : Expr}
    (actual : ContextMatches ctx (.action (.runIn receiver scope)) n)
    (printed : decorate sig ctx (.call (.ident "Effect.withFiber") [.arrowBlock []
      [.exprStmt (.call (.ident "Fiber.runIn") [input,scopeExpr]),
        .ret (.ident "Effect.void")] none]) = .ok out) :
    EraseTermTypes.eraseNode n out = .call (.ident "Effect.withFiber") [.arrowBlock []
      [.exprStmt (.call (.ident "Fiber.runIn") [input,scopeExpr]),
        .ret (.ident "Effect.void")] none] := by
  rcases actual with ⟨node, depth⟩
  aesop (config := {maxRuleApplicationDepth := 100}) (add norm simp [decorate, node, need, withHeadTypes, bind, Except.bind,
    eraseNode_bare_call, Effect4.Codegen.eraseNode_rawRunIn]) (add safe apply [EraseTermTypes.eraseNode_runIn])

end Effect4.Codegen.PrintEliminators

namespace Effect4.Codegen.PrintEliminators
open TypeScript Effect4.Program Template Templates

-- Placement: exact-codecs R8, successful typed-print erasure.
-- Consumer: decorate_table_inst_erases' finite header cases.
-- Only structural target shapes are extracted; no child typing premise enters.
theorem inst_call1_shape (n : Nat) (τ : Subst) (head : String) (a : Tpl) (y : Expr)
    (printed : inst n τ (call head [a]) = some y) :
    ∃ x, y = .call (.ident head) [x] := by
  aesop (add norm simp [call, tpls, inst, insts, Option.bind_eq_some_iff])

theorem inst_call2_shape (n : Nat) (τ : Subst) (head : String) (a b : Tpl) (y : Expr)
    (printed : inst n τ (call head [a,b]) = some y) :
    ∃ x z, y = .call (.ident head) [x,z] := by
  aesop (add norm simp [call, tpls, inst, insts, Option.bind_eq_some_iff])

theorem inst_call3_shape (n : Nat) (τ : Subst) (head : String) (a b c : Tpl) (y : Expr)
    (printed : inst n τ (call head [a,b,c]) = some y) :
    ∃ x z w, y = .call (.ident head) [x,z,w] := by
  aesop (add norm simp [call, tpls, inst, insts, Option.bind_eq_some_iff])

theorem inst_option_shape (n : Nat) (τ : Subst) (y : Expr)
    (printed : inst n τ (call "optionCase" [h 0,.arrow (h 2),lam (h 3)]) = some y) :
    ∃ input left right, y = .call (.ident "optionCase")
      [input,.arrow none left,.lambda (params n [0]) right none] := by
  aesop (add norm simp [call, tpls, h, lam, inst, insts, Option.bind_eq_some_iff])

theorem inst_acquireRelease_shape (n : Nat) (τ : Subst) (y : Expr)
    (printed : inst n τ (call "Effect.acquireRelease" [h 0,.lambda [0,1] (h 1)]) = some y) :
    ∃ acquire release, y = .call (.ident "Effect.acquireRelease")
      [acquire,.lambda (params n [0,1]) release none] := by
  aesop (add norm simp [call, tpls, h, inst, insts, Option.bind_eq_some_iff])

theorem inst_tag_shape (n : Nat) (τ : Subst) (tag : String) (y : Expr)
    (literal : lookup τ 1 = some (.str tag))
    (printed : inst n τ (call "caseTag" [h 0,.strHole 1,lam (h 2),lam (h 3)]) = some y) :
    ∃ input left right, y = .call (.ident "caseTag")
      [input,.str tag,.lambda (params n [0]) left none,.lambda (params n [0]) right none] := by
  aesop (add norm simp [call, tpls, h, lam, inst, insts, literal, Option.bind_eq_some_iff])

theorem inst_recordTag_shape (n : Nat) (τ : Subst) (tag : String) (y : Expr)
    (literal : lookup τ 1 = some (.expr (.str tag)))
    (printed : inst n τ (call "caseTagR" [h 0,h 1,lam (h 2),lam (h 3)]) = some y) :
    ∃ input left right, y = .call (.ident "caseTagR")
      [input,.str tag,.lambda (params n [0]) left none,.lambda (params n [0]) right none] := by
  aesop (add norm simp [call, tpls, h, lam, inst, insts, literal, Option.bind_eq_some_iff])

end Effect4.Codegen.PrintEliminators

namespace Effect4.Codegen.PrintEliminators
open TypeScript Effect4.Program Template Templates
variable {Op : Type}

-- Placement: exact-codecs R8, successful typed-print erasure.
-- Consumer: decorate_table_inst_erases' source-specific shape extraction.
-- These compute existing row selection only. They add no source admission.

theorem find_site_option (scrutinee : Term) (left right : Eff Op) :
    Templates.table.find? (fun row => row.selects .eff "select"
      ([.term scrutinee,.decision .option,.child .eff left,.child .eff right] : List (ArgF Op (EffSelfCarrier Op)))) =
      some ⟨.eff,"select",[(1,.is (.decision .option))],.tpl (call "optionCase" [h 0,.arrow (h 2),lam (h 3)])⟩ := rfl

theorem find_site_tag (scrutinee : Term) (tag : String) (left right : Eff Op) :
    Templates.table.find? (fun row => row.selects .eff "select"
      ([.term scrutinee,.decision (.tag tag),.child .eff left,.child .eff right] : List (ArgF Op (EffSelfCarrier Op)))) =
      some ⟨.eff,"select",[(1,.decisionTag)],.tpl (call "caseTag" [h 0,.strHole 1,lam (h 2),lam (h 3)])⟩ := rfl

theorem find_site_recordTag (scrutinee : Term) (tag : String) (left right : Eff Op) :
    Templates.table.find? (fun row => row.selects .eff "select"
      ([.term scrutinee,.decision (.recordTag tag),.child .eff left,.child .eff right] : List (ArgF Op (EffSelfCarrier Op)))) =
      some ⟨.eff,"select",[(1,.decisionRecordTag)],.tpl (call "caseTagR" [h 0,h 1,lam (h 2),lam (h 3)])⟩ := rfl

theorem find_site_scoped (child : Eff Op) :
    Templates.table.find? (fun row => row.selects .eff "scoped"
      ([.child .eff child] : List (ArgF Op (EffSelfCarrier Op)))) =
      some ⟨.eff,"scoped",[],.tpl (call "Effect.scoped" [h 0])⟩ := rfl

theorem find_site_acquireRelease (acquire release : Eff Op) :
    Templates.table.find? (fun row => row.selects .eff "acquireRelease"
      ([.child .eff acquire,.child .eff release] : List (ArgF Op (EffSelfCarrier Op)))) =
      some ⟨.eff,"acquireRelease",[],.tpl (call "Effect.acquireRelease" [h 0,.lambda [0,1] (h 1)])⟩ := rfl

theorem find_site_interrupt (receiver : Term) :
    Templates.table.find? (fun row => row.selects .action "interrupt"
      ([.term receiver] : List (ArgF Op (EffSelfCarrier Op)))) =
      some ⟨.action,"interrupt",[],.tpl (call "Fiber.interrupt" [h 0])⟩ := rfl

theorem find_site_awaitAll (receivers : Term) :
    Templates.table.find? (fun row => row.selects .action "awaitAll"
      ([.term receivers] : List (ArgF Op (EffSelfCarrier Op)))) =
      some ⟨.action,"awaitAll",[],.tpl (call "Fiber.awaitAll" [h 0])⟩ := rfl

theorem find_site_interruptAll (receivers : Term) :
    Templates.table.find? (fun row => row.selects .action "interruptAll"
      ([.term receivers,.optTerm none] : List (ArgF Op (EffSelfCarrier Op)))) =
      some ⟨.action,"interruptAll",[(1,.is .noTerm)],.tpl (call "Fiber.interruptAll" [h 0])⟩ := rfl

theorem find_site_interruptAllAs (receivers interruptor : Term) :
    Templates.table.find? (fun row => row.selects .action "interruptAll"
      ([.term receivers,.optTerm (some interruptor)] : List (ArgF Op (EffSelfCarrier Op)))) =
      some ⟨.action,"interruptAll",[(1,.someTerm)],.tpl (call "Fiber.interruptAllAs" [h 0,h 1])⟩ := rfl

theorem find_site_closeScope (scope exit : Term) :
    Templates.table.find? (fun row => row.selects .action "closeScope"
      ([.term scope,.term exit] : List (ArgF Op (EffSelfCarrier Op)))) =
      some ⟨.action,"closeScope",[],.tpl (call "Scope.close" [h 0,h 1])⟩ := rfl

theorem find_site_runIn (receiver scope : Term) :
    Templates.table.find? (fun row => row.selects .action "runIn"
      ([.term receiver,.term scope] : List (ArgF Op (EffSelfCarrier Op)))) =
      some ⟨.action,"runIn",[],.tpl (call "Effect.withFiber" [.arrowBlock [] (stmtsOf [.exprStmt (call "Fiber.runIn" [h 0,h 1]),.ret (.ident "Effect.void")])])⟩ := rfl

theorem find_site_awaitFiber (receiver : Term) (mode : Effect4.Supervision.ObserverMode) :
    Templates.table.find? (fun row => row.selects .eff "awaitFiber"
      ([.term receiver,.mode mode] : List (ArgF Op (EffSelfCarrier Op)))) =
      some ⟨.eff,"awaitFiber",[(1,.is (.mode mode))],.tpl
        (call (match mode with | .joinEffect => "Fiber.join" | .awaitValue => "Fiber.await") [h 0])⟩ := by
  cases mode <;> rfl

-- Fork's head chooses the existing daemon classifier; stored options stay unchanged.
theorem find_site_fork (child : Eff Op) (options : Effect4.Supervision.ForkOptions) :
    Templates.table.find? (fun row => row.selects .action "fork"
      ([.child .eff child,.forkOptions options] : List (ArgF Op (EffSelfCarrier Op)))) =
      some ⟨.action,"fork",[(1,.daemon options.daemon)],.tpl
        (call (if options.daemon then "Effect.forkDetach" else "Effect.forkChild") [h 0,h 1])⟩ := by
  cases options with
  | mk startImmediately daemon maskMode => cases daemon <;> rfl

theorem find_site_forkIn (child : Eff Op) (options : Effect4.Supervision.ForkOptions) (scope : Term) :
    Templates.table.find? (fun row => row.selects .action "forkIn"
      ([.child .eff child,.forkOptions options,.term scope] : List (ArgF Op (EffSelfCarrier Op)))) =
      some ⟨.action,"forkIn",[(1,.daemon options.daemon)],
        if options.daemon then .tpl (call "Effect.forkIn" [h 0,h 2,h 1]) else .refuse "forkIn:child"⟩ := by
  cases options with
  | mk startImmediately daemon maskMode => cases daemon <;> rfl

theorem find_site_forkScoped (child : Eff Op) (options : Effect4.Supervision.ForkOptions) :
    Templates.table.find? (fun row => row.selects .action "forkScoped"
      ([.child .eff child,.forkOptions options] : List (ArgF Op (EffSelfCarrier Op)))) =
      some ⟨.action,"forkScoped",[(1,.daemon options.daemon)],
        if options.daemon then .tpl (call "Effect.forkScoped" [h 0,h 1]) else .refuse "forkScoped:child"⟩ := by
  cases options with
  | mk startImmediately daemon maskMode => cases daemon <;> rfl

end Effect4.Codegen.PrintEliminators

namespace Effect4.Codegen.PrintEliminators
open TypeScript Effect4.Program Template Templates
variable {Op : Type}

-- Placement: exact-codecs R8, successful typed-print erasure.
-- Consumer: decorate_table_inst_erases' two tag cases.
-- The source decision controls the literal read by the node inverse.
theorem typedArgs_tag_capture (sig : Signature Op) (alg : EffAlgebra Op TCarrier)
    (ctx : Context Op) (fam : EffFam) (n : Nat) (out : RowOut)
    (args : List (ArgF Op (EffSelfCarrier Op))) (path : List Nat) (tag : String)
    (τ : Subst) (source : args[1]? = some (.decision (.tag tag)))
    (printed : printArgs sig ctx fam n out
      (atAddress path (args.map (ArgF.fold alg)) 0) 0 = .ok τ) :
    lookup τ 1 = some (.str tag) := by
  have actual := Effect4.Codegen.atAddress_fold_leaf_for alg sig path args 1
    (.decision (.tag tag)) (by intro childFam child eq; cases eq) source
  have atOne := (printArgs_lookup ctx _ 0 τ printed).1 1
    (.decision (.tag tag)) actual
  simp only [printArg, Templates.printArg, Except.ok.injEq] at atOne
  exact atOne.symm

theorem typedArgs_recordTag_capture (sig : Signature Op) (alg : EffAlgebra Op TCarrier)
    (ctx : Context Op) (fam : EffFam) (n : Nat) (out : RowOut)
    (args : List (ArgF Op (EffSelfCarrier Op))) (path : List Nat) (tag : String)
    (τ : Subst) (source : args[1]? = some (.decision (.recordTag tag)))
    (printed : printArgs sig ctx fam n out
      (atAddress path (args.map (ArgF.fold alg)) 0) 0 = .ok τ) :
    lookup τ 1 = some (.expr (.str tag)) := by
  have actual := Effect4.Codegen.atAddress_fold_leaf_for alg sig path args 1
    (.decision (.recordTag tag)) (by intro childFam child eq; cases eq) source
  have atOne := (printArgs_lookup ctx _ 0 τ printed).1 1
    (.decision (.recordTag tag)) actual
  simp only [printArg, Templates.printArg, Except.ok.injEq] at atOne
  exact atOne.symm

end Effect4.Codegen.PrintEliminators

namespace Effect4.Codegen.PrintEliminators
open TypeScript Effect4.Program Template Templates
variable {Op : Type}

-- Placement: exact-codecs R8, successful Program.printTyped erasure.
-- Consumer: SiteExprRigid and site_action_normalized_head.
-- Actual successful printArgs fixes source scalars before template instantiation.
-- Rigidity excludes the transparent withFiber child, handled by the lower-family induction.
theorem decorate_table_inst_erases
    (sig : Signature Op) (alg : EffAlgebra Op TCarrier) (ctx : Context Op) (n : Nat)
    (fam : EffFam) (source : EffSelfCarrier Op fam)
    (ctor : String) (args : List (ArgF Op (EffSelfCarrier Op)))
    (row : Templates.Row) (t : Tpl) (path : List Nat) (τ : Subst) (y x : Expr)
    (actualCtxnode : ctx.node = Effect4.Codegen.nodeOfFamily fam source)
    (actualDepth : ctx.env.length = n)
    (viewed : view fam source = (ctor,args))
    (selected : Templates.table.find? (fun row => row.selects fam ctor args) = some row)
    (output : row.out = .tpl t) (rigid : t.rigid = true)
    (typedArgs : printArgs sig ctx fam n (.tpl t)
      (atAddress path (args.map (ArgF.fold alg)) 0) 0 = .ok τ)
    (instantiated : inst n τ t = some y)
    (decorated : decorate sig ctx y = .ok x) : EraseTermTypes.eraseNode n x = y := by
  have member := List.mem_of_find?_eq_some selected
  have unchanged := Effect4.Codegen.eraseNode_of_table_inst member output rigid instantiated
  cases fam with
  | eff =>
    change view_eff source = (ctor,args) at viewed
    cases source with
    | select scrutinee decision left right =>
      cases decision with
      | bool =>
        have same : y = x := by
          simpa only [decorate, actualCtxnode, Effect4.Codegen.nodeOfFamily,
            pure, Except.pure, Except.ok.injEq] using decorated
        subst x
        exact unchanged
      | option =>
        simp only [view_eff, Prod.mk.injEq] at viewed
        rcases viewed with ⟨rfl,rfl⟩
        have same := Option.some.inj (selected.symm.trans (find_site_option scrutinee left right))
        subst row
        cases output
        obtain ⟨input,l,r,rfl⟩ := inst_option_shape n τ y instantiated
        exact decorate_option_erases sig ctx n scrutinee left right input l r ⟨actualCtxnode,actualDepth⟩ decorated
      | tag tag =>
        simp only [view_eff, Prod.mk.injEq] at viewed
        rcases viewed with ⟨rfl,rfl⟩
        have same := Option.some.inj (selected.symm.trans (find_site_tag scrutinee tag left right))
        subst row
        cases output
        have literal := typedArgs_tag_capture sig alg ctx .eff n _ _ path tag τ rfl typedArgs
        obtain ⟨input,l,r,rfl⟩ := inst_tag_shape n τ tag y literal instantiated
        exact decorate_tag_erases sig ctx n scrutinee tag left right input l r ⟨actualCtxnode,actualDepth⟩ decorated
      | recordTag tag =>
        simp only [view_eff, Prod.mk.injEq] at viewed
        rcases viewed with ⟨rfl,rfl⟩
        have same := Option.some.inj (selected.symm.trans (find_site_recordTag scrutinee tag left right))
        subst row
        cases output
        have literal := typedArgs_recordTag_capture sig alg ctx .eff n _ _ path tag τ rfl typedArgs
        obtain ⟨input,l,r,rfl⟩ := inst_recordTag_shape n τ tag y literal instantiated
        exact decorate_recordTag_erases sig ctx n scrutinee tag left right input l r ⟨actualCtxnode,actualDepth⟩ decorated
    | awaitFiber receiver mode =>
      simp only [view_eff, Prod.mk.injEq] at viewed
      rcases viewed with ⟨rfl,rfl⟩
      have same := Option.some.inj (selected.symm.trans (find_site_awaitFiber receiver mode))
      subst row
      cases output
      obtain ⟨input,rfl⟩ := inst_call1_shape n τ _ _ y instantiated
      cases mode <;>
        exact decorate_awaitFiber_erases sig ctx n receiver _ input
          ⟨actualCtxnode,actualDepth⟩ decorated
    | «scoped» child =>
      simp only [view_eff, Prod.mk.injEq] at viewed
      rcases viewed with ⟨rfl,rfl⟩
      have same := Option.some.inj (selected.symm.trans (find_site_scoped child))
      subst row
      cases output
      obtain ⟨input,rfl⟩ := inst_call1_shape n τ _ _ y instantiated
      exact decorate_scoped_erases sig ctx n child input ⟨actualCtxnode,actualDepth⟩ decorated
    | acquireRelease acquire release =>
      simp only [view_eff, Prod.mk.injEq] at viewed
      rcases viewed with ⟨rfl,rfl⟩
      have same := Option.some.inj (selected.symm.trans (find_site_acquireRelease acquire release))
      subst row
      cases output
      obtain ⟨first,second,rfl⟩ := inst_acquireRelease_shape n τ y instantiated
      exact decorate_acquireRelease_erases sig ctx n acquire release first second
        ⟨actualCtxnode,actualDepth⟩ decorated
    | _ =>
      have same : y = x := by
        simpa only [decorate, actualCtxnode, Effect4.Codegen.nodeOfFamily,
          pure, Except.pure, Except.ok.injEq] using decorated
      subst x
      exact unchanged
  | action =>
    change view_action source = (ctor,args) at viewed
    cases source with
    | fork child options =>
      simp only [view_action, Prod.mk.injEq] at viewed
      rcases viewed with ⟨rfl,rfl⟩
      have same := Option.some.inj (selected.symm.trans (find_site_fork child options))
      subst row
      cases output
      obtain ⟨input,opts,rfl⟩ := inst_call2_shape n τ _ _ _ y instantiated
      exact decorate_fork_erases sig ctx n child options input opts
        ⟨actualCtxnode,actualDepth⟩ decorated
    | forkIn child options scope =>
      simp only [view_action, Prod.mk.injEq] at viewed
      rcases viewed with ⟨rfl,rfl⟩
      have same := Option.some.inj (selected.symm.trans (find_site_forkIn child options scope))
      subst row
      cases daemon : options.daemon with
      | false =>
        simp only [daemon, Bool.false_eq_true, ↓reduceIte] at output
        cases output
      | true =>
        simp only [daemon, ↓reduceIte] at output
        cases output
        obtain ⟨input,scopeExpr,opts,rfl⟩ := inst_call3_shape n τ _ _ _ _ y instantiated
        exact decorate_forkIn_erases sig ctx n child options scope input opts scopeExpr
          ⟨actualCtxnode,actualDepth⟩ decorated
    | forkScoped child options =>
      simp only [view_action, Prod.mk.injEq] at viewed
      rcases viewed with ⟨rfl,rfl⟩
      have same := Option.some.inj (selected.symm.trans (find_site_forkScoped child options))
      subst row
      cases daemon : options.daemon with
      | false =>
        simp only [daemon, Bool.false_eq_true, ↓reduceIte] at output
        cases output
      | true =>
        simp only [daemon, ↓reduceIte] at output
        cases output
        obtain ⟨input,opts,rfl⟩ := inst_call2_shape n τ _ _ _ y instantiated
        exact decorate_forkScoped_erases sig ctx n child options input opts
          ⟨actualCtxnode,actualDepth⟩ decorated
    | interrupt receiver =>
      simp only [view_action, Prod.mk.injEq] at viewed
      rcases viewed with ⟨rfl,rfl⟩
      have same := Option.some.inj (selected.symm.trans (find_site_interrupt receiver))
      subst row
      cases output
      obtain ⟨input,rfl⟩ := inst_call1_shape n τ _ _ y instantiated
      exact decorate_interrupt_erases sig ctx n receiver input ⟨actualCtxnode,actualDepth⟩ decorated
    | awaitAll receivers =>
      simp only [view_action, Prod.mk.injEq] at viewed
      rcases viewed with ⟨rfl,rfl⟩
      have same := Option.some.inj (selected.symm.trans (find_site_awaitAll receivers))
      subst row
      cases output
      obtain ⟨input,rfl⟩ := inst_call1_shape n τ _ _ y instantiated
      exact decorate_awaitAll_erases sig ctx n receivers input ⟨actualCtxnode,actualDepth⟩ decorated
    | closeScope scope exit =>
      simp only [view_action, Prod.mk.injEq] at viewed
      rcases viewed with ⟨rfl,rfl⟩
      have same := Option.some.inj (selected.symm.trans (find_site_closeScope scope exit))
      subst row
      cases output
      obtain ⟨first,second,rfl⟩ := inst_call2_shape n τ _ _ _ y instantiated
      exact decorate_closeScope_erases sig ctx n scope exit first second ⟨actualCtxnode,actualDepth⟩ decorated
    | runIn receiver scope =>
      simp only [view_action, Prod.mk.injEq] at viewed
      rcases viewed with ⟨rfl,rfl⟩
      have same := Option.some.inj (selected.symm.trans (find_site_runIn receiver scope))
      subst row
      cases output
      change inst n τ Effect4.Codegen.rawRunInTpl = some y at instantiated
      obtain ⟨first,second,rfl⟩ := Effect4.Codegen.inst_rawRunIn_shape instantiated
      exact decorate_runIn_erases sig ctx n receiver scope first second ⟨actualCtxnode,actualDepth⟩ decorated
    | interruptAll receivers interruptor =>
      cases interruptor with
      | none =>
        simp only [view_action, Prod.mk.injEq] at viewed
        rcases viewed with ⟨rfl,rfl⟩
        have same := Option.some.inj (selected.symm.trans (find_site_interruptAll receivers))
        subst row
        cases output
        obtain ⟨input,rfl⟩ := inst_call1_shape n τ _ _ y instantiated
        exact decorate_interruptAll_erases sig ctx n receivers input
          ⟨actualCtxnode,actualDepth⟩ decorated
      | some interruptor =>
        simp only [view_action, Prod.mk.injEq] at viewed
        rcases viewed with ⟨rfl,rfl⟩
        have same := Option.some.inj (selected.symm.trans (find_site_interruptAllAs receivers interruptor))
        subst row
        cases output
        obtain ⟨input,who,rfl⟩ := inst_call2_shape n τ _ _ _ y instantiated
        exact decorate_interruptAllAs_erases sig ctx n receivers interruptor input who
          ⟨actualCtxnode,actualDepth⟩ decorated
    | _ =>
      have same : y = x := by
        simpa only [decorate, actualCtxnode, Effect4.Codegen.nodeOfFamily,
          pure, Except.pure, Except.ok.injEq] using decorated
      subst x
      exact unchanged
  | layer | layers | effs | stmts | stmt =>
    have same : y = x := by
      simpa only [decorate, actualCtxnode, Effect4.Codegen.nodeOfFamily,
        pure, Except.pure, Except.ok.injEq] using decorated
    subst x
    exact unchanged

end Effect4.Codegen.PrintEliminators


/-!
Placement: exact-codecs, R8, helper of the full P2b typed-print erasure connector.
Consumer: the structural connector's rowCall branch.
Reach: actual successful PrintEliminators.perform, at its actual node and environment.
The request and operation binder erase by the integrated generated term fold law.
The ordinary row reader retains its original readable and LawfulSpelling premises.
No premise assumes an erasure equation. This file states no compiler or host result.
-/

set_option autoImplicit false

namespace Effect4.Codegen.P2bRowSupport

open TypeScript Effect4.Program Template Templates Effect4.Laws.Auto

variable {Op : Type}

theorem except_bind_identity {α ε : Type} (m : Except ε α) :
    m.bind (fun x => Except.ok x) = m := by
  cases m <;> rfl

-- This helper is definitionally the local tupleArgs in PrintEliminators.row.
def tupleArgs (sig : Signature Op) (env : TyEnv) (q : Term) : Except PrintRefusal (List Expr) := do
  match pairArgs? q with
  | some (a, b) => return [← PrintEliminators.term sig env false a,
      ← PrintEliminators.term sig env false b]
  | none =>
    let value ← PrintEliminators.term sig env false q
    return [.call (.ident "fst") [value], .call (.ident "snd") [value]]

theorem tupleArgs_erases (sig : Signature Op) (env : TyEnv) (q : Term) {xs : List Expr}
    (hp : tupleArgs sig env q = .ok xs) :
    xs.map (EraseTermTypes.eraseTerm env.length) = printTupleArgs env.length q := by
  unfold tupleArgs at hp
  cases pair : pairArgs? q with
  | some ab =>
    rcases ab with ⟨a, b⟩
    rw [pair] at hp
    obtain ⟨x, hx, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
    obtain ⟨y, hy, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
    simp only [pure_eq_ok] at hp
    subst xs
    simp only [List.map_cons, List.map_nil, printTupleArgs, pair,
      EraseTermTypes.eraseTerm_printTerm sig a env false hx,
      EraseTermTypes.eraseTerm_printTerm sig b env false hy]
  | none =>
    rw [pair] at hp
    obtain ⟨x, hx, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
    simp only [pure_eq_ok] at hp
    subst xs
    have hf := EraseTermTypes.callInverse_erasedApp env.length "fst" (.cons q .nil)
    have hs := EraseTermTypes.callInverse_erasedApp env.length "snd" (.cons q .nil)
    simp only [printTerms, List.map_cons, List.map_nil,
      EraseTermTypes.eraseTerm_printTerm_identity] at hf hs
    simp only [List.map_cons, List.map_nil, printTupleArgs, pair,
      EraseTermTypes.eraseTerm_call, EraseTermTypes.eraseTerm_ident,
      EraseTermTypes.eraseTerm_printTerm sig q env false hx, hf, hs]

-- This helper is definitionally the method arm of PrintEliminators.row.
def method (sig : Signature Op) (env : TyEnv) (r : Effect4.Program.Row)
    (receiver args : Term) : Except PrintRefusal Expr := do
  let targetExpr ← PrintEliminators.term sig env false receiver
  let argsRow := methodArgsRow r
  let argsExpr ← if argsRow.shape = .tupleCall then tupleArgs sig env args
    else if argsRow.request = .unit then pure []
    else do pure [← PrintEliminators.term sig env false args]
  let declared ← PrintEliminators.need r.spelling (rowTypeArgs r)
  if declared.isEmpty then return .method targetExpr r.spelling (argsExpr ++ r.trailing.map RowArg.print)
  else return .call (.generic (.member targetExpr r.spelling) declared) (argsExpr ++ r.trailing.map RowArg.print)

theorem need_some {α : Type} {name : String} {value : Option α} {x : α}
    (hp : PrintEliminators.need name value = .ok x) : value = some x := by
  cases value with
  | none => exact nomatch hp
  | some v => cases hp; rfl

theorem methodArgs_erases (sig : Signature Op) (env : TyEnv) (r : Effect4.Program.Row)
    (args : Term) {xs : List Expr}
    (hp : (if (methodArgsRow r).shape = .tupleCall then tupleArgs sig env args
      else if (methodArgsRow r).request = .unit then pure []
      else do pure [← PrintEliminators.term sig env false args]) = .ok xs) :
    (xs ++ r.trailing.map RowArg.print).map (EraseTermTypes.eraseTerm env.length) =
      printMethodArgs env.length r args := by
  unfold printMethodArgs
  split at hp
  · rename_i hs
    rw [if_pos hs]
    rw [List.map_append, tupleArgs_erases sig env args hp, eraseTerm_trailing]
  · rename_i hs
    rw [if_neg hs]
    split at hp
    · rename_i hu
      rw [if_pos hu]
      simp only [pure_eq_ok] at hp
      subst xs
      exact eraseTerm_trailing env.length r.trailing
    · rename_i hu
      rw [if_neg hu]
      obtain ⟨x, hx, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
      simp only [pure_eq_ok] at hp
      subst xs
      simp only [List.cons_append, List.nil_append, List.map_cons,
        EraseTermTypes.eraseTerm_printTerm sig args env false hx, eraseTerm_trailing]

theorem method_as_bind (sig : Signature Op) (env : TyEnv) (r : Effect4.Program.Row)
    (receiver args : Term) :
    method sig env r receiver args =
      (PrintEliminators.term sig env false receiver).bind (fun targetExpr =>
        (if (methodArgsRow r).shape = .tupleCall then tupleArgs sig env args
          else if (methodArgsRow r).request = .unit then pure []
          else do pure [← PrintEliminators.term sig env false args]).bind (fun argsExpr =>
            (PrintEliminators.need r.spelling (rowTypeArgs r)).bind (fun declared =>
              if declared.isEmpty then .ok (.method targetExpr r.spelling (argsExpr ++ r.trailing.map RowArg.print))
              else .ok (.call (.generic (.member targetExpr r.spelling) declared) (argsExpr ++ r.trailing.map RowArg.print))))) := by
  unfold method
  cases hr : PrintEliminators.term sig env false receiver with
  | error why => rfl
  | ok targetExpr =>
    dsimp only [bind, Except.bind]
    by_cases hs : (methodArgsRow r).shape = .tupleCall
    · simp only [if_pos hs]
      cases tupleArgs sig env args <;> rfl
    · simp only [if_neg hs]
      by_cases hu : (methodArgsRow r).request = .unit
      · simp only [if_pos hu]
        rfl
      · simp only [if_neg hu]
        cases PrintEliminators.term sig env false args <;> rfl

theorem method_erases (sig : Signature Op) (env : TyEnv) (r : Effect4.Program.Row)
    (receiver args : Term) {x : Expr} (hp : method sig env r receiver args = .ok x) :
    printMethod env.length r receiver args = .ok (eraseRowChildren env.length x) := by
  rw [method_as_bind] at hp
  obtain ⟨receiverExpr, hr, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
  obtain ⟨argsExpr, ha, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
  obtain ⟨declared, hd, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
  have hr' := EraseTermTypes.eraseTerm_printTerm sig receiver env false hr
  have ha' := methodArgs_erases sig env r args ha
  have hd' := need_some hd
  cases declared with
  | nil =>
    simp only [List.isEmpty_nil, ↓reduceIte, Except.ok.injEq] at hp
    subst x
    simp only [printMethod, hd', eraseRowChildren]
    rw [hr', ha']
  | cons ty tys =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hp
    subst x
    simp only [printMethod, hd', eraseRowChildren, EraseTermTypes.eraseTerm, mapCalls_generic]
    change (Except.ok (Expr.call (.generic (.member (printTerm env.length receiver) r.spelling) (ty :: tys))
      (printMethodArgs env.length r args)) : Except PrintRefusal Expr) =
      Except.ok (Expr.call (.generic (.member (EraseTermTypes.eraseTerm env.length receiverExpr) r.spelling)
        (ty :: tys)) ((argsExpr ++ r.trailing.map RowArg.print).map (EraseTermTypes.eraseTerm env.length)))
    rw [hr', ha']

theorem row_erases (sig : Signature Op) (env : TyEnv) (r : Effect4.Program.Row)
    (request : Term) {x : Expr} (hp : PrintEliminators.row sig env r request = .ok x) :
    printRow env.length r request = .ok (eraseRowChildren env.length x) := by
  cases shape : r.shape with
  | value =>
    simp only [PrintEliminators.row, shape, pure_eq_ok] at hp
    subst x
    simp only [printRow, shape, eraseRowChildren]
  | call =>
    simp only [PrintEliminators.row, shape] at hp
    obtain ⟨head, hh, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
    have hh' := eraseTerm_printRowHead env.length r hh
    split at hp
    · rename_i hu
      simp only [pure_eq_ok] at hp
      subst x
      simp only [printRow, shape, hh, bind, Except.bind, hu, ↓reduceIte,
        eraseRowChildren, hh', eraseTerm_trailing]
    · rename_i hu
      obtain ⟨value, hv, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
      simp only [pure_eq_ok] at hp
      subst x
      simp only [printRow, shape, hh, bind, Except.bind, hu, ↓reduceIte,
        eraseRowChildren, hh', List.map_cons, eraseTerm_trailing,
        EraseTermTypes.eraseTerm_printTerm sig request env false hv]
  | tupleCall =>
    simp only [PrintEliminators.row, shape] at hp
    obtain ⟨head, hh, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
    obtain ⟨values, hv, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
    change tupleArgs sig env request = .ok values at hv
    simp only [pure_eq_ok] at hp
    subst x
    simp only [printRow, shape, hh, bind, Except.bind, eraseRowChildren,
      eraseTerm_printRowHead env.length r hh, List.map_append,
      tupleArgs_erases sig env request hv, eraseTerm_trailing]
  | method =>
    cases pair : pairArgs? request with
    | none =>
      simp only [PrintEliminators.row, shape, pair, Option.getD_none] at hp
      change method sig env r (.app "fst" (.cons request .nil))
        (.app "snd" (.cons request .nil)) = .ok x at hp
      simp only [printRow, shape, pair]
      exact method_erases sig env r _ _ hp
    | some ab =>
      rcases ab with ⟨receiver, args⟩
      simp only [PrintEliminators.row, shape, pair, Option.getD_some] at hp
      change method sig env r receiver args = .ok x at hp
      simp only [printRow, shape, pair]
      exact method_erases sig env r receiver args hp

theorem withHeadTypes_erases (n : Nat) (spelling : String) (types : List TypeRef)
    {base x : Expr} (hp : withHeadTypes spelling types base = .ok x) :
    withHeadTypes spelling types (eraseRowChildren n base) = .ok (eraseRowChildren n x) := by
  fun_cases withHeadTypes spelling types base
  · cases hp
    simp only [eraseRowChildren, EraseTermTypes.eraseTerm, mapCalls_ident, mapCalls_generic,
      withHeadTypes]
  · cases hp
    simp only [eraseRowChildren, EraseTermTypes.eraseTerm, mapCalls_generic,
      withHeadTypes]
    rfl
  all_goals aesop (add norm simp withHeadTypes)

theorem withFunction_erases (n : Nat) (spelling : String) {fn plain x : Expr}
    (hp : withFunction spelling fn plain = .ok x) :
    withFunction spelling (EraseTermTypes.eraseTerm n fn) (eraseRowChildren n plain) =
      .ok (eraseRowChildren n x) := by
  fun_cases withFunction spelling fn plain
  · cases hp
    simp only [withFunction, eraseRowChildren, List.map_append, List.map_cons, List.map_nil]
  · cases hp
    simp only [withFunction, eraseRowChildren, List.map_append, List.map_cons, List.map_nil]
  all_goals aesop (add norm simp withFunction)

theorem targets_writeTys (tys : List Ty) {xs : List TypeRef}
    (hp : tys.mapM PrintEliminators.target = .ok xs) : Classes.writeTys tys = some xs := by
  induction tys generalizing xs with
  | nil =>
    simp only [List.mapM_nil, pure_eq_ok] at hp
    subst xs
    rfl
  | cons ty tys ih =>
    simp only [List.mapM_cons] at hp
    obtain ⟨x, hx, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
    obtain ⟨tail, ht, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
    simp only [pure_eq_ok] at hp
    subst xs
    unfold PrintEliminators.target at hx
    cases hty : Types.ofTy ty with
    | none => rw [hty] at hx; exact nomatch hx
    | some value =>
      rw [hty] at hx
      cases hx
      simp only [Classes.writeTys, hty, ih ht, bind, Option.bind_some]

-- The two call helpers name precisely the first part of the actual perform printers.
def call (sig : Signature Op) (env : TyEnv) (op : Op) (request : Term)
    (ann : Option (List Ty)) : Except PrintRefusal Expr := do
  let base ← PrintEliminators.row sig env (sig.rowOf op) request
  let owned := sig.typeArgsOf op
  match ann with
  | some (ty :: tys) => do
    if owned.isEmpty && (sig.rowOf op).typeArgs.isEmpty then
      withHeadTypes (sig.rowOf op).spelling (← (ty :: tys).mapM PrintEliminators.target) base
    else throw (.typeSpelling (sig.rowOf op).spelling)
  | _ => do
    if owned.isEmpty then pure base
    else withHeadTypes (sig.rowOf op).spelling (← owned.mapM PrintEliminators.target) base

def rawCall (sig : Signature Op) (n : Nat) (op : Op) (request : Term) :
    Option (List Ty) → Except PrintRefusal Expr
  | some (ty :: tys) =>
    if (sig.typeArgsOf op).isEmpty && (sig.rowOf op).typeArgs.isEmpty then
      match Classes.writeTys (ty :: tys) with
      | some targets => (printRow n (sig.rowOf op) request).bind
          (withHeadTypes (sig.rowOf op).spelling targets)
      | none => .error (.typeSpelling (sig.rowOf op).spelling)
    else .error (.typeSpelling (sig.rowOf op).spelling)
  | _ => printCall sig n op request

theorem call_erases (sig : Signature Op) (env : TyEnv) (op : Op) (request : Term)
    (ann : Option (List Ty)) {x : Expr} (hp : call sig env op request ann = .ok x) :
    rawCall sig env.length op request ann = .ok (eraseRowChildren env.length x) := by
  unfold call at hp
  obtain ⟨base, hb, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
  dsimp only at hp
  have hb' := row_erases sig env (sig.rowOf op) request hb
  have ordinary (hp : (if (sig.typeArgsOf op).isEmpty then pure base
      else do
        let targets ← (sig.typeArgsOf op).mapM PrintEliminators.target
        withHeadTypes (sig.rowOf op).spelling targets base) = .ok x) :
      printCall sig env.length op request = .ok (eraseRowChildren env.length x) := by
    cases owned : sig.typeArgsOf op with
    | nil =>
      simp only [owned, List.isEmpty_nil, ↓reduceIte, pure_eq_ok] at hp
      subst x
      simp only [printCall, owned]
      exact hb'
    | cons ty tys =>
      simp only [owned, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hp
      obtain ⟨targets, ht, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
      have hw := targets_writeTys (ty :: tys) ht
      simp only [printCall, owned, hw, hb', Except.bind]
      exact withHeadTypes_erases env.length _ _ hp
  cases ann with
  | none => exact ordinary hp
  | some tys =>
    cases tys with
    | nil => exact ordinary hp
    | cons ty tys =>
      change (if (sig.typeArgsOf op).isEmpty && (sig.rowOf op).typeArgs.isEmpty then
        (do
          let targets ← (ty :: tys).mapM PrintEliminators.target
          withHeadTypes (sig.rowOf op).spelling targets base)
        else throw (.typeSpelling (sig.rowOf op).spelling)) = .ok x at hp
      split at hp
      · rename_i eligible
        obtain ⟨targets, ht, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
        have hw := targets_writeTys (ty :: tys) ht
        simp only [rawCall, eligible, ↓reduceIte, hw, hb', Except.bind]
        exact withHeadTypes_erases env.length _ _ hp
      · exact nomatch hp

theorem perform_as_call (sig : Signature Op) (ctx : PrintEliminators.Context Op)
    (op : Op) (request : Term) (ann : Option (List Ty)) :
    PrintEliminators.perform sig ctx op request ann =
      (call sig ctx.env op request ann).bind (fun base =>
        match sig.termOf op with
        | none => .ok base
        | some b => do
          let env ← PrintEliminators.need "operation term" (ctx.node.extSlotEnv sig ctx.env .opTerm)
          withFunction (sig.rowOf op).spelling (Binders.write ctx.env.length [0] (← PrintEliminators.term sig env false b.term)) base) := by
  unfold PrintEliminators.perform call
  cases hr : PrintEliminators.row sig ctx.env (sig.rowOf op) request with
  | error why => rfl
  | ok base =>
    cases ann with
    | none =>
      dsimp only [bind, Except.bind]
      by_cases ho : (sig.typeArgsOf op).isEmpty = true
      · simp only [if_pos ho]
        rfl
      · simp only [if_neg ho]
        cases ht : (sig.typeArgsOf op).mapM PrintEliminators.target with
        | error why => rfl
        | ok targets => cases withHeadTypes (sig.rowOf op).spelling targets base <;> rfl
    | some tys =>
      cases tys with
      | nil =>
        dsimp only [bind, Except.bind]
        by_cases ho : (sig.typeArgsOf op).isEmpty = true
        · simp only [if_pos ho]
          rfl
        · simp only [if_neg ho]
          cases ht : (sig.typeArgsOf op).mapM PrintEliminators.target with
          | error why => rfl
          | ok targets => cases withHeadTypes (sig.rowOf op).spelling targets base <;> rfl
      | cons ty tys =>
        dsimp only [bind, Except.bind]
        by_cases ho : ((sig.typeArgsOf op).isEmpty && (sig.rowOf op).typeArgs.isEmpty) = true
        · simp only [if_pos ho]
          cases ht : (ty :: tys).mapM PrintEliminators.target with
          | error why => rfl
          | ok targets => cases withHeadTypes (sig.rowOf op).spelling targets base <;> rfl
        · simp only [if_neg ho]
          rfl

theorem rawPerform_as_call (sig : Signature Op) (n : Nat) (op : Op) (request : Term)
    (ann : Option (List Ty)) :
    Templates.printPerformAt sig n op request ann =
      (rawCall sig n op request ann).bind (fun base =>
        match sig.termOf op with
        | none => .ok base
        | some b => withFunction (sig.rowOf op).spelling (Binders.write n [0] (printTerm (n + 1) b.term)) base) := by
  cases ann with
  | none =>
    cases h : sig.termOf op <;>
      simp only [Templates.printPerformAt, rawCall, printPerform, h, except_bind_identity]
  | some tys =>
    cases tys with
    | nil =>
      cases h : sig.termOf op <;>
        simp only [Templates.printPerformAt, rawCall, printPerform, h, except_bind_identity]
    | cons ty tys =>
      simp only [Templates.printPerformAt, rawCall]
      split
      · cases hw : Classes.writeTys (ty :: tys) with
        | none => cases sig.termOf op <;> rfl
        | some targets =>
          cases hb : sig.termOf op with
          | none =>
            exact (except_bind_identity ((printRow n (sig.rowOf op) request).bind
              (withHeadTypes (sig.rowOf op).spelling targets))).symm
          | some b => rfl
      · rfl

theorem opTerm_env_length (sig : Signature Op) (ctx : PrintEliminators.Context Op)
    (op : Op) (request : Term) {env : TyEnv}
    (hn : ctx.node = .eff (.perform op request))
    (hp : ctx.node.extSlotEnv sig ctx.env .opTerm = some env) :
    env.length = ctx.env.length + 1 := by
  rw [hn] at hp
  simp only [Node.extSlotEnv] at hp
  split at hp
  · split at hp
    · split at hp
      · cases hp
        simp only [List.length_append, List.length_cons, List.length_nil]
      · exact nomatch hp
    · exact nomatch hp
  · exact nomatch hp

theorem binder_erases (sig : Signature Op) (ctx : PrintEliminators.Context Op)
    (op : Op) (request : Term) {env : TyEnv} {t : Term} {x : Expr}
    (hn : ctx.node = .eff (.perform op request))
    (he : ctx.node.extSlotEnv sig ctx.env .opTerm = some env)
    (hp : PrintEliminators.term sig env false t = .ok x) :
    EraseTermTypes.eraseTerm ctx.env.length (Binders.write ctx.env.length [0] x) =
      Binders.write ctx.env.length [0] (printTerm (ctx.env.length + 1) t) := by
  have hlen := opTerm_env_length sig ctx op request hn he
  have ht := EraseTermTypes.eraseTerm_printTerm sig t env false hp
  rw [hlen] at ht
  simp only [Binders.write, Template.params, List.map_cons, List.map_nil,
    EraseTermTypes.eraseTerm_lambda, List.length_cons, List.length_nil, Nat.zero_add, ht]

theorem perform_erases_children (sig : Signature Op) (ctx : PrintEliminators.Context Op)
    (op : Op) (request : Term) (ann : Option (List Ty)) {x : Expr}
    (hn : ctx.node = .eff (.perform op request))
    (hp : PrintEliminators.perform sig ctx op request ann = .ok x) :
    Templates.printPerformAt sig ctx.env.length op request ann = .ok (eraseRowChildren ctx.env.length x) := by
  rw [perform_as_call] at hp
  obtain ⟨base, hb, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
  have hb' := call_erases sig ctx.env op request ann hb
  rw [rawPerform_as_call, hb']
  simp only [Except.bind]
  cases term : sig.termOf op with
  | none =>
    simp only [term, Except.ok.injEq] at hp
    subst x
    rfl
  | some b =>
    rw [term] at hp
    obtain ⟨env, he, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
    obtain ⟨value, hv, hp⟩ := Effect4.Laws.Auto.bind_eq_ok.mp hp
    have he' := need_some he
    have hf := binder_erases sig ctx op request hn he' hv
    change withFunction (sig.rowOf op).spelling
      (Binders.write ctx.env.length [0] (printTerm (ctx.env.length + 1) b.term))
      (eraseRowChildren ctx.env.length base) = .ok (eraseRowChildren ctx.env.length x)
    rw [← hf]
    exact withFunction_erases ctx.env.length _ hp

end Effect4.Codegen.P2bRowSupport

namespace Effect4.Codegen

open TypeScript Effect4.Program Template Templates

variable {Op : Type} {classes : Classes.Classes} {sig : Signature Op}
  {spell : String → List RowArg → Option Op}

/-- The P2b row template erases typed term children before the unchanged complete-call reader.
Placement: exact-codecs, R8; consumer: the full typedSitesAlg structural erasure connector. -/
theorem eraseExprRow_typedPerform (hl : LawfulSpelling sig spell) {n : Nat} {op : Op}
    {request : Term} {ctx : PrintEliminators.Context Op}
    (hnode : ctx.node = .eff (.perform op request)) (henv : ctx.env.length = n)
    (hd : sig.dom op = true)
    (hreq : requestReadable (sig.rowOf op) n request = true) (hc : request.covers classes = true)
    (hu : request.unannotated = true)
    (htypes : typeArgsReadable (sig.rowOf op) (sig.typeArgsOf op) = true)
    (hterm : termReadable classes n (sig.rowOf op) ((sig.termOf op).map (·.term)) = true)
    {annotation : Option (List Ty)} {typed : Expr}
    (printed : PrintEliminators.perform sig ctx op request annotation = .ok typed)
    (row : Templates.Row) (family : row.fam = .eff) (output : row.out = .rowCall)
    (child : EffFam → Nat → (y : Expr) → sizeOf y < sizeOf typed → Expr)
    (children : EffFam → Nat → (ys : List Expr) → sizeOf ys < sizeOf typed → List Expr)
    (block : Nat → (ss : List TypeScript.Stmt) → sizeOf ss < sizeOf typed → List TypeScript.Stmt)
    (same : (fam' : EffFam) → famRank fam' < famRank .eff → Nat → Option Expr) :
    ∃ plain, printPerform sig n op request = .ok plain ∧
      eraseExprRow classes sig spell .eff n typed row child children block same = some plain := by
  have erasedChildren := P2bRowSupport.perform_erases_children sig ctx op request annotation hnode printed
  rw [henv] at erasedChildren
  obtain ⟨plain, ordinary, erased⟩ :=
    eraseRowJoin_printPerformAt_total hl hd hreq hc hu htypes hterm erasedChildren
  refine ⟨plain, ordinary, ?_⟩
  simp only [eraseExprRow, family, output, ↓reduceIte, erased,
    readPerform_printPerform hl hd hreq hc hu htypes hterm ordinary]

end Effect4.Codegen

namespace Effect4.Codegen.P2bRowSupport

open TypeScript Effect4.Program Template Templates
open TypedRowShapeSupport

variable {Op : Type} {sig : Signature Op}

theorem rowHeadOwned_of_erased {n : Nat} {spelling : String} {x : Expr}
    (owned : rowHeadOwned spelling (eraseRowChildren n x)) : rowHeadOwned spelling x := by
  constructor
  · intro name args heq
    subst x
    exact owned.1 name (args.map (EraseTermTypes.eraseTerm n)) rfl
  · intro name types args heq
    subst x
    exact owned.2 name types (args.map (EraseTermTypes.eraseTerm n)) rfl

theorem nodeLike_erased (n : Nat) (x : Expr) : nodeLike (eraseRowChildren n x) = nodeLike x := by
  cases x <;> rfl

theorem head_erased {n : Nat} {x : Expr} {name : String}
    (head : exprHead? x = some name) : exprHead? (eraseRowChildren n x) = some name := by
  fun_cases exprHead? x
  · exact head
  · exact head
  all_goals aesop (add norm simp exprHead?)

theorem rawPerformAt_head {n : Nat} {op : Op} {request : Term}
    {ann : Option (List Ty)} {x : Expr}
    (hp : Templates.printPerformAt sig n op request ann = .ok x) :
    exprHead? x = none ∨ exprHead? x = some (sig.rowOf op).spelling := by
  cases ann with
  | none => exact printPerform_head hp
  | some tys =>
    cases tys with
    | nil => exact printPerform_head hp
    | cons ty tys =>
      obtain ⟨plain, target, targets, _, hhead⟩ := printPerformAt_head hp
      exact Or.inl (withHeadTypes_head hhead).1

end Effect4.Codegen.P2bRowSupport

namespace Effect4.Codegen

open TypeScript Effect4.Program Template Templates TypedRowShapeSupport

variable {Op : Type} {sig : Signature Op} {classes : Classes.Classes}
  {spell : String → List RowArg → Option Op}

/-- The actual P2b row owns its head before its typed term children erase.
Placement: exact-codecs, R8; consumer: rowCall first-match separation in the full connector. -/
theorem typedPerform_rowHeadOwned {ctx : PrintEliminators.Context Op} {op : Op} {request : Term}
    {ann : Option (List Ty)} {x : Expr} (hn : ctx.node = .eff (.perform op request))
    (hp : PrintEliminators.perform sig ctx op request ann = .ok x) :
    rowHeadOwned (sig.rowOf op).spelling x :=
  P2bRowSupport.rowHeadOwned_of_erased (printPerformAt_rowHeadOwned
    (P2bRowSupport.perform_erases_children sig ctx op request ann hn hp))

theorem typedPerform_nodeLike {ctx : PrintEliminators.Context Op} {op : Op} {request : Term}
    {ann : Option (List Ty)} {x : Expr} (hn : ctx.node = .eff (.perform op request))
    (hp : PrintEliminators.perform sig ctx op request ann = .ok x) : nodeLike x = true := by
  have h := printPerformAt_nodeLike
    (P2bRowSupport.perform_erases_children sig ctx op request ann hn hp)
  rw [P2bRowSupport.nodeLike_erased] at h
  exact h

theorem typedPerform_no_reserved (hl : LawfulSpelling sig spell)
    {ctx : PrintEliminators.Context Op} {op : Op} {request : Term}
    {ann : Option (List Ty)} {x : Expr} (hn : ctx.node = .eff (.perform op request))
    (hp : PrintEliminators.perform sig ctx op request ann = .ok x)
    (d : Nat) (t : Tpl) (h : String) (hh : t.head? = some h) (hres : h ∈ reserved) :
    matchT d t x = none := by
  cases hm : matchT d t x with
  | none => rfl
  | some substitution =>
    have head := head_of_match d t x substitution hm hh
    have erasedHead := P2bRowSupport.head_erased (n := ctx.env.length) head
    have image := P2bRowSupport.rawPerformAt_head
      (P2bRowSupport.perform_erases_children sig ctx op request ann hn hp)
    rcases image with absent | owned
    · rw [erasedHead] at absent
      exact nomatch absent
    · rw [erasedHead] at owned
      have spelling : h = (sig.rowOf op).spelling := Option.some.inj owned
      rw [spelling] at hres
      exact False.elim (hl.spelling_not_reserved op hres)

theorem eraseNode_typedPerform (hl : LawfulSpelling sig spell)
    {ctx : PrintEliminators.Context Op} {op : Op} {request : Term}
    {ann : Option (List Ty)} {x : Expr} (hn : ctx.node = .eff (.perform op request))
    (hp : PrintEliminators.perform sig ctx op request ann = .ok x) (d : Nat) :
    EraseTermTypes.eraseNode d x = x := by
  have owned := typedPerform_rowHeadOwned hn hp
  apply eraseNode_of_genericHead_not_reserved
  · intro name args heq
    rw [owned.1 name args heq]
    exact hl.spelling_not_reserved op
  · intro name types args heq
    rw [owned.2 name types args heq]
    exact hl.spelling_not_reserved op

theorem eraseT_action_none_of_typedPerform (hl : LawfulSpelling sig spell)
    {ctx : PrintEliminators.Context Op} {op : Op} {request : Term}
    {ann : Option (List Ty)} {x : Expr} (hn : ctx.node = .eff (.perform op request))
    (hp : PrintEliminators.perform sig ctx op request ann = .ok x) (d : Nat) :
    eraseT classes sig spell .action d x = none := by
  rw [eraseT, eraseNode_typedPerform hl hn hp d, List.findSome?_eq_none_iff]
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
        (typedPerform_no_reserved hl hn hp d t h hh (List.mem_of_elem_eq_true hres))
    · rename_i name hout
      exact eraseExprRow_none_of_refuse hout
    · cases hshape

end Effect4.Codegen

set_option autoImplicit false
namespace Effect4.Codegen
open TypeScript Effect4.Program Template Templates
variable {Op : Type} {classes : Classes.Classes} {sig : Signature Op}
  {spell : String → List RowArg → Option Op} {ann : List Nat → Option (List Ty)}
  {root : Eff Op} {env0 : TyEnv}

/-- An actual successfully decorated action retains its table-owned head after normalization.
Placement: exact-codecs R8; consumer: transparent effect-to-action table separation. -/
theorem site_action_normalized_head
    {path : List Nat} {n : Nat} {source : ActionTerm Op} {x : Expr}
    (focus : SiteFocused root sig env0 path .action source n)
    (printed : PrintedCaptureAt (typedSitesAlg sig ann
      (PrintEliminators.contextAtTable (annotate sig env0 root) root)) path n .action source (.expr x))
    (readable : ReadableAt classes sig .action source n) :
    ∃ head, exprHead? (EraseTermTypes.eraseNode n x) = some head ∧ head ∈ actionHeads := by
  obtain ⟨ctor, args, viewed⟩ : ∃ ctor args, view .action source = (ctor, args) := ⟨_, _, rfl⟩
  have built : build .action ctor args = some source := by
    have h := build_view .action source
    rwa [viewed] at h
  obtain ⟨d, hd⟩ := readable
  have dom := congrFun (cata_build (domLayer classes sig) .action ctor args source built) n
  have domain := dom.symm.trans hd
  obtain ⟨row, selected, rowCase⟩ := rowDom_inv domain
  have selectSource : Templates.table.find? (fun row => row.selects .action ctor args) = some row := by
    simpa only [selects_fold] using selected
  have member := List.mem_of_find?_eq_some selectSource
  have selectedSource := List.find?_some selectSource
  have family := (selects_fam_ctor selectedSource).1
  have actionShape := table_fact table_actionHeaded member
  simp only [actionRowHeaded, family, bne_self_eq_false, Bool.false_or] at actionShape
  rcases rowCase with ⟨t, output, _⟩ | ⟨_, _, output, _⟩
  · rw [output] at actionShape
    simp only [Bool.and_eq_true, Option.any_eq_true] at actionShape
    obtain ⟨rigid, head, headAt, _⟩ := actionShape
    obtain ⟨ctx, τ, y, found, arguments, instantiated, decorated⟩ :=
      site_template_inv (Or.inr (Or.inl rfl)) built selectSource output printed
    obtain ⟨node, depth⟩ := site_context_matches focus found
    have normal := PrintEliminators.decorate_table_inst_erases sig
      (typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root))
      ctx n .action source ctor args row t path τ y x node depth viewed selectSource output
      rigid arguments instantiated decorated
    refine ⟨head, ?_, ?_⟩
    · rw [normal]
      exact head_of_inst n τ t y instantiated headAt
    · exact mem_actionHeads member family output headAt
  · rw [output] at actionShape
    cases actionShape

end Effect4.Codegen

set_option autoImplicit false
namespace Effect4.Codegen
open TypeScript Effect4.Program Template Templates
variable {Op : Type} {classes : Classes.Classes} {sig : Signature Op}
  {spell : String → List RowArg → Option Op} {ann : List Nat → Option (List Ty)}
  {root : Eff Op} {env0 : TyEnv}
/-! Placement: exact-codecs R8; expression source-image erasure.
Consumer: SitesEraseUpTo and the public successful typed print connector.
The source focus is discharged through actual checked contexts. -/
set_option maxHeartbeats 4000000 in
theorem eraseT_site_print (lawful : LawfulSpelling sig spell)
    {fam : EffFam} {path : List Nat} {n : Nat} {e : EffSelfCarrier Op fam} {x : Expr}
    (hchild : ∀ path fam d (source : EffSelfCarrier Op fam) y,
      sizeOf y < sizeOf x → SiteFocused root sig env0 path fam source d → ReadableAt classes sig fam source d →
      PrintedCaptureAt (typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root)) path d fam source (.expr y) →
      (∃ plain, eraseT classes sig spell fam d y = some plain ∧ PrintsTo sig d fam source (.expr plain)) ∧
        nodeLike (EraseTermTypes.eraseNode d y) = true)
    (hchildren : ∀ path fam d (source : EffSelfCarrier Op fam) ys,
      sizeOf ys < sizeOf x → SiteFocused root sig env0 path fam source d → ReadableAt classes sig fam source d →
      PrintedCaptureAt (typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root)) path d fam source (.exprs ys) →
      PrintsTo sig d fam source (.exprs (eraseSpine classes sig spell fam d ys)))
    (hblock : ∀ path d (source : Stmts Op) ss,
      sizeOf ss < sizeOf x → SiteFocused root sig env0 path .stmts source d → ReadableAt classes sig .stmts source d →
      PrintedCaptureAt (typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root)) path d .stmts source (.stmts ss) →
      PrintsTo sig d .stmts source (.stmts (eraseStmts classes sig spell d ss)))
    (hsame : ∀ fam', famRank fam' < famRank fam → ∀ path d source,
      SiteFocused root sig env0 path fam' source d → ReadableAt classes sig fam' source d → PrintedCaptureAt (typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root)) path d fam' source (.expr x) →
      (∃ plain, eraseT classes sig spell fam' d x = some plain ∧ PrintsTo sig d fam' source (.expr plain)) ∧
        nodeLike (EraseTermTypes.eraseNode d x) = true)
    (focus : SiteFocused root sig env0 path fam e n)
    (family : fam = .eff ∨ fam = .action ∨ fam = .layer)
    (typed : PrintedCaptureAt (typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root)) path n fam e (.expr x))
    (readable : ReadableAt classes sig fam e n) :
    (∃ plain, eraseT classes sig spell fam n x = some plain ∧ PrintsTo sig n fam e (.expr plain)) ∧
      nodeLike (EraseTermTypes.eraseNode n x) = true := by
  obtain ⟨ctor, args, hview⟩ : ∃ ctor args, view fam e = (ctor, args) := ⟨_, _, rfl⟩
  have hbuild : build fam ctor args = some e := by
    have h := build_view fam e
    rwa [hview] at h
  have hsorts : argSorts fam ctor = some (args.map argSortOf) := by
    have h := argSorts_view fam e
    rwa [hview] at h
  obtain ⟨plain, ordinary⟩ := readable_expr_prints family readable
  have hp : tableLayer.rowPrint sig fam ctor (args.map (ArgF.fold (printAlg sig))) n = .ok plain := by
    have h := congrFun (cata_build (tableLayer sig) fam ctor args e hbuild) n
    rcases family with rfl | rfl | rfl <;> simp only [PrintsTo, cataFam] at ordinary h <;>
      exact h.symm.trans ordinary
  obtain ⟨ctx, hctx⟩ := printedCaptureAt_context typed
  obtain ⟨hctxnode, hctxdepth⟩ := site_context_matches focus hctx
  obtain ⟨d, hd⟩ := readable
  have hdom : domLayer.rowDom classes sig fam ctor (args.map (ArgF.fold (readableAlg classes sig))) n = some d := by
    have h := congrFun (cata_build (domLayer classes sig) fam ctor args e hbuild) n
    rcases family with rfl | rfl | rfl <;> simp only [cataFam] at h <;> exact h.symm.trans hd
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
  rcases hcase with ⟨t, τplain, hout, hτplain, hinstplain⟩ | ⟨op, request, hout, hargs, hpplain⟩
  · rcases hcase' with ⟨t', hout', hr⟩ | ⟨_, _, hout', _⟩
    swap; · rw [hout] at hout'; cases hout'
    rw [hout, RowOut.tpl.injEq] at hout'
    subst hout'
    obtain ⟨ctx', τ, y, hctx', hτ, hinst, hdecorate⟩ :=
      site_template_inv family hbuild hfindSource hout typed
    have sameCtx : ctx' = ctx := Option.some.inj (hctx'.symm.trans hctx)
    subst ctx'
    by_cases hrigid : t.rigid = true
    · have hnormal := PrintEliminators.decorate_table_inst_erases sig
        (typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root)) ctx n fam e ctor args row t path τ y x
        hctxnode hctxdepth hview hfindSource hout hrigid hτ hinst hdecorate
      obtain ⟨erased, node⟩ := eraseT_site_rigid_step family focus hview hfindSource hk
        hsortsRow hout hrigid (by rw [hfamrow, hout]; exact hτ) hinst hnormal
        (by rw [hfamrow, hout]; exact hr) (by rw [hfamrow, hout]; exact hτplain)
        hinstplain hchild hchildren hblock
      exact ⟨⟨plain, erased, ordinary⟩, by rwa [hnormal]⟩
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
            have hp0 := (PrintEliminators.printArgs_lookup ctx _ 0 τ hτ).1 0
              (.child .action (cata_action (typedSitesAlg sig ann
                (PrintEliminators.contextAtTable (annotate sig env0 root) root)) source (path ++ [0]))) rfl
            simp only [inst] at hinst
            have hlook : lookup τ 0 = some (.expr y) := by
              revert hinst; cases lookup τ 0 <;> aesop
            rw [Nat.add_zero, argSortOf, hlook] at hp0
            simp only [PrintEliminators.printArg] at hp0
            have hpa := printedCaptureAt_of_printArg hp0
            have hlevel : (RowOut.tpl (.hole 0)).levelAt 0 = 0 := rfl
            rw [hlevel] at hpa
            have hra : ReadableAt classes sig .action source (argDepth .eff (.child .action) n 0) := by
              have h := argsReadable_at _ 0 0 (ArgF.fold (readableAlg classes sig) (.child .action source)) hr rfl
              rw [Nat.add_zero, argSortOf_fold, argSortOf, hlevel] at h
              exact readableAt_of_argReadable h
            have lower : famRank .action < famRank .eff := by decide
            have childCtx := printedCaptureAt_context hpa
            obtain ⟨ctxChild, ctxFound⟩ := childCtx
            have childFocus := siteFocused_child focus hview hfindSource
              (i := 0) (childFam := .action) (child := source) rfl ctxFound
              (fun _ refused => nomatch hout.symm.trans refused)
            rw [hout, hlevel] at childFocus
            have he : e = .withFiber source := by
              (cases e <;> cases hview)
              rfl
            have decorated : y = x := by
              simpa only [PrintEliminators.decorate, hctxnode, he, nodeOfFamily,
                pure, Except.pure, Except.ok.injEq] using hdecorate
            subst y
            obtain ⟨⟨erased, herase, hplain⟩, hnode⟩ := hsame .action lower _ _ source childFocus hra hpa
            obtain ⟨head, hhead, haction⟩ := site_action_normalized_head childFocus hpa hra
            have normal := EraseTermTypes.eraseNode_idempotent n x
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
            have erasedNormal : eraseT classes sig spell .eff n (EraseTermTypes.eraseNode n x) = some plain := by
              refine eraseT_of_row normal hk (fun j hj rj hrj => ?_) ?_
              · rcases hother j hj rj hrj with hne | apart
                · exact eraseExprRow_none_of_fam hne
                · exact erase_earlier_none_action apart hout (by rw [hsortsRow, hact]) hhead haction
              · simp only [eraseExprRow, hfamrow, hout, ↓reduceIte,
                  show argSorts .eff row.ctor = some [.child .action] from by rw [hsortsCtor, hact],
                  Tpl.rigid, Bool.false_eq_true, ↓reduceDIte, lower, matchT, argDepth,
                  Nat.add_zero]
                rw [eraseT_normalize_root]
                exact herase
            refine ⟨⟨plain, ?_, ordinary⟩, hnode⟩
            rw [← eraseT_normalize_root classes sig spell .eff n x]
            exact erasedNormal
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
            have hp0 := (PrintEliminators.printArgs_lookup ctx _ 0 τ hτ).1 0 (.path p) rfl
            simp only [Nat.add_zero, PrintEliminators.printArg, printArg, Except.ok.injEq] at hp0
            have hy : y = .ident (LayerTerm.refName p) := by
              simp only [inst] at hinst
              rw [← hp0] at hinst
              exact (Option.some.inj hinst).symm
            have hpplain := (printArgs_lookup _ 0 τplain hτplain).1 0 (.path p) rfl
            simp only [Nat.add_zero, printArg, Except.ok.injEq] at hpplain
            have hplain : plain = .ident (LayerTerm.refName p) := by
              simp only [inst] at hinstplain
              rw [← hpplain] at hinstplain
              exact (Option.some.inj hinstplain).symm
            have decorated : y = x := by
              simpa only [PrintEliminators.decorate, hctxnode, nodeOfFamily,
                pure, Except.pure, Except.ok.injEq] using hdecorate
            have hx : x = .ident (LayerTerm.refName p) := decorated.symm.trans hy
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
    simp only [PrintedCaptureAt] at typed
    have equation := typedSites_cata_build sig ann
      (PrintEliminators.contextAtTable (annotate sig env0 root) root) .eff "perform"
      [.op op, .term request] (.perform op request) rfl path
    simp only [cataFam] at equation
    rw [equation, hctx] at typed
    change PrintEliminators.perform sig ctx op request (ann path) = .ok x at typed
    obtain ⟨ordinaryCall, hpCall, atRow⟩ := eraseExprRow_typedPerform lawful hctxnode hctxdepth hd' hreq hcover hun htypes hterm
      typed row hfamily hout
      (fun fam d y _ => (eraseT classes sig spell fam d y).getD y)
      (fun fam d ys _ => eraseSpine classes sig spell fam d ys)
      (fun d ss _ => eraseStmts classes sig spell d ss)
      (fun fam' _ d => eraseT classes sig spell fam' d x)
    have heq : ordinaryCall = plain := Except.ok.inj (hpCall.symm.trans hpplain)
    subst ordinaryCall
    refine ⟨⟨plain, eraseT_of_row (eraseNode_typedPerform lawful hctxnode typed n) hk
        (fun j hj rj hrj => ?_) atRow, hpplain⟩,
      by rw [EraseTermTypes.eraseNode_nodeLike]; exact typedPerform_nodeLike hctxnode typed⟩
    rcases hother j hj rj hrj with hne | apart
    · exact eraseExprRow_none_of_fam hne
    · exact erase_earlier_none_rowCall apart hout
        (fun t head headed reserved => typedPerform_no_reserved lawful hctxnode typed n t head headed reserved)
        (fun _ d => eraseT_action_none_of_typedPerform lawful hctxnode typed d)

end Effect4.Codegen

set_option autoImplicit false
namespace Effect4.Codegen
open TypeScript Effect4.Program Template Templates
variable {Op : Type} {classes : Classes.Classes} {sig : Signature Op}
  {spell : String → List RowArg → Option Op} {ann : List Nat → Option (List Ty)}
  {root : Eff Op} {env0 : TyEnv}
/-! Placement: exact-codecs R8; actual source/address full erasure induction.
Consumer: public typed print erasure and old read-law composition.
Measure: actual target image size, then the existing family rank. -/
theorem eraseT_site_print_step (lawful : LawfulSpelling sig spell) {m : Nat}
    (ih : ∀ smaller, smaller < m → SitesEraseUpTo classes sig spell root env0 ann smaller)
    {fam : EffFam} {path : List Nat} {n : Nat} {e : EffSelfCarrier Op fam} {x : Expr}
    (size : sizeOf x ≤ m)
    (same : ∀ fam', famRank fam' < famRank fam → ∀ path d source,
      SiteFocused root sig env0 path fam' source d → ReadableAt classes sig fam' source d → PrintedCaptureAt (typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root)) path d fam' source (.expr x) →
      (∃ plain, eraseT classes sig spell fam' d x = some plain ∧ PrintsTo sig d fam' source (.expr plain)) ∧
        nodeLike (EraseTermTypes.eraseNode d x) = true)
    (focus : SiteFocused root sig env0 path fam e n)
    (readable : ReadableAt classes sig fam e n)
    (typed : PrintedCaptureAt (typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root)) path n fam e (.expr x)) :
    (∃ plain, eraseT classes sig spell fam n x = some plain ∧ PrintsTo sig n fam e (.expr plain)) ∧
      nodeLike (EraseTermTypes.eraseNode n x) = true := by
  have family : fam = .eff ∨ fam = .action ∨ fam = .layer := by
    cases fam <;> simp only [PrintedCaptureAt] at typed ⊢ <;> aesop
  exact eraseT_site_print lawful
    (fun path fam d source y smaller hf hr hp =>
      (ih (sizeOf y) (by omega)).1 fam path d source y (Nat.le_refl _) hf hr hp)
    (fun path fam d source ys smaller hf hr hp =>
      (ih (sizeOf ys) (by omega)).2.1 fam path d source ys (Nat.le_refl _) hf hr hp)
    (fun path d source ss smaller hf hr hp =>
      (ih (sizeOf ss) (by omega)).2.2 path d source ss (Nat.le_refl _) hf hr hp)
    same focus family typed readable

theorem sitesErasesUpTo (lawful : LawfulSpelling sig spell) (m : Nat) :
    SitesEraseUpTo classes sig spell root env0 ann m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    have low : ∀ fam, famRank fam = 0 → ∀ path n (e : EffSelfCarrier Op fam) x,
        sizeOf x ≤ m → SiteFocused root sig env0 path fam e n → ReadableAt classes sig fam e n → PrintedCaptureAt (typedSitesAlg sig ann (PrintEliminators.contextAtTable (annotate sig env0 root) root)) path n fam e (.expr x) →
        (∃ plain, eraseT classes sig spell fam n x = some plain ∧ PrintsTo sig n fam e (.expr plain)) ∧
          nodeLike (EraseTermTypes.eraseNode n x) = true :=
      fun fam rank path n e x size hf hr hp =>
        eraseT_site_print_step lawful ih size (fun fam' lower => absurd lower (by omega)) hf hr hp
    refine ⟨fun fam path n e x size hf hr hp => ?_, ?_, ?_⟩
    · exact eraseT_site_print_step lawful ih size
        (fun fam' lower path d source hf' hr' hp' =>
          low fam' (by have h := famRank_le_one fam; omega) path d source x size hf' hr' hp') hf hr hp
    · exact eraseSiteSpine_print_step
        (fun fam path n e y smaller hf hr hp =>
          ((ih (sizeOf y) smaller).1 fam path n e y (Nat.le_refl _) hf hr hp).1)
        (fun fam path n e ys smaller hf hr hp =>
          (ih (sizeOf ys) smaller).2.1 fam path n e ys (Nat.le_refl _) hf hr hp)
    · apply eraseSiteStmts_print_step lawful
      · intro path n st s declared smaller hf hr hp
        exact eraseSiteStmt_print
          (fun path fam d source y smaller' hf' hr' hp' => by
            obtain ⟨plain, erased, printed⟩ :=
              ((ih (sizeOf y) (by omega)).1 fam path d source y (Nat.le_refl _) hf' hr' hp').1
            rw [erased, Option.getD_some]
            exact printed)
          (fun path fam d source ys smaller' hf' hr' hp' =>
            (ih (sizeOf ys) (by omega)).2.1 fam path d source ys (Nat.le_refl _) hf' hr' hp')
          (fun path d source ss smaller' hf' hr' hp' =>
            (ih (sizeOf ss) (by omega)).2.2 path d source ss (Nat.le_refl _) hf' hr' hp') hf hp hr
      · exact fun path n e ss smaller hf hr hp =>
          (ih (sizeOf ss) smaller).2.2 path n e ss (Nat.le_refl _) hf hr hp

end Effect4.Codegen

set_option autoImplicit false
namespace Effect4.Codegen
open TypeScript Effect4.Program Template Templates
variable {Op : Type} {classes : Classes.Classes} {sig : Signature Op}
  {spell : String → List RowArg → Option Op}

/-- The full site printer reconstructs today's ordinary print after named join erasure.
Placement: exact-codecs R8; consumer: Program.printTyped and the existing reader laws. -/
@[semantics "exact-codecs" (requirement := R8)]
theorem eraseJoinArgs_printTypedSitesAt (lawful : LawfulSpelling sig spell)
    {env0 : TyEnv} {e : Eff Op} {ann : List Nat → Option (List Ty)}
    (readable : Readable classes sig env0.length e = true) {x : Expr}
    (printed : printTypedSitesAt sig ann (PrintEliminators.contextAtTable (annotate sig env0 e) e)
      env0.length e = .ok x) :
    print sig env0.length e = .ok (eraseJoinArgs classes sig spell env0.length x) := by
  obtain ⟨plain, erased, ordinary⟩ :=
    ((sitesErasesUpTo (root := e) (env0 := env0) (ann := ann) lawful (sizeOf x)).1
      .eff [] env0.length e x (Nat.le_refl _) (siteFocused_root e sig env0)
      (by unfold ReadableAt; simpa only [Readable, cataFam, Option.isSome_iff_exists] using readable)
      printed).1
  simp only [eraseJoinArgs, erased, Option.getD_some]
  exact ordinary

/-- Every successful public typed print erases to the existing ordinary print.
The exact old readable and spelling premises remain visible (exact-codecs, R8). -/
@[semantics "exact-codecs" (requirement := R8)]
theorem eraseJoinArgs_printTyped (lawful : LawfulSpelling sig spell)
    {env0 : TyEnv} {e : Eff Op} (readable : Readable classes sig env0.length e = true)
    {x : Expr} (printed : Program.printTyped sig env0 e = .ok x) :
    print sig env0.length e = .ok (eraseJoinArgs classes sig spell env0.length x) := by
  unfold Program.printTyped at printed
  dsimp only at printed
  split at printed
  · exact eraseJoinArgs_printTypedSitesAt lawful readable printed
  · exact eraseJoinArgs_printTypedAt lawful readable printed

/-- The existing reader reads every successful public typed print after named erasure.
The theorem carries the existing read_print fragment (exact-codecs, R8). -/
@[semantics "exact-codecs" (requirement := R8)]
theorem readTyped_printTyped (lawful : LawfulSpelling sig spell)
    {env0 : TyEnv} {e : Eff Op} (readable : Readable classes sig env0.length e = true)
    {x : Expr} (printed : Program.printTyped sig env0 e = .ok x) :
    readTyped classes sig spell env0.length x = .ok e :=
  readTyped_of_print_erasure lawful readable (eraseJoinArgs_printTyped lawful readable printed)

end Effect4.Codegen
