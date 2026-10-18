import Effect4.Program.Typing.Support

/-!
# Certified checking

`CheckInput` names a module check or a part check. `run` uses the existing checking owners.
`Oracle` carries pointwise agreement with `run`. `Checked` records valid answers in request order.
`Memo` learns only these traces and answers through a rule that carries its agreement law.

The generated OCaml interface seals `Oracle`, `Checked`, `Memo`, and `HitRule` as whole packages.
The native boundary uses the existing LCNF translation trust. No arbitrary callback is certified.

Placement: `checker-oracle-agrees`, host-session-protocol, R6/R14.
`Oracle.eq_uncached` states the claim. The trace and memo proofs construct its consumer packages.
Their observation is each check's exact verdict. They assert no native execution or progress theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace Effect4.Program
open Effect4 Effect4.Program Effect4.Store

/-! ## 1. Checking -/

namespace Check

/-- Everything one check reads; its canonical bytes are a complete key. -/
inductive CheckInput where
  /-- a sketch through its layer references, at the application extended by its holes; the root
  address `[]` is always checked through this key -/
  | module (app : SigApp) (holes : RowTable) (program : NativeEff)
  /-- a part of an expansion, or a filling inside its candidate's expansion, in its context -/
  | part (sig : SigData) (env : TyEnv) (program : NativeEff)
deriving DecidableEq

/-- A check's answer, rooted at the empty path. -/
structure Verdict where
  result : Except TypeRefusal EffTy
  table : List Table.Entry

/-- The uncached meaning: the existing owners, unchanged. -/
def run : CheckInput → Verdict
  | .module app holes p =>
      let s : Sketch := { program := p, holes := holes }
      ⟨s.sourceCheck app, s.sourceAnnotate app⟩
  | .part d env q =>
      let o := Annotate.check d.signature env [] q
      ⟨o.2, o.1⟩

namespace Internal
/-- A part's verdict placed at its base address: every refusal and every entry below `base`, by
the one prefix rule (`Located.under`). -/
def place (base : List Nat) (v : Verdict) : Verdict :=
  ⟨v.result.mapError (Located.under base), v.table.map ((fun e => ⟨base ++ e.path, e.env, e.result.map (fun r => r.mapError (Located.under base))⟩))⟩

inductive DepRole where
  | body (index : Nat) | main | layers
deriving DecidableEq

structure Dep where
  role : DepRole
  base : List Nat
  input : CheckInput

def bodyDeps (app : SigApp) (holes : RowTable) (allDecls : List DefDecl) :
    List DefDecl → Effs NativeOp → Nat → List Nat → List Dep
  | d :: ds, .cons b bs, index, base =>
    ⟨.body index, base ++ [0],
      .part ⟨app, holes, .body allDecls d.params⟩ [d.request.normalize] b⟩ ::
      bodyDeps app holes allDecls ds bs (index + 1) (base ++ [1])
  | _, _, _, _ => []

def deps : CheckInput → List Dep
  | .part .. => []
  | .module app holes p =>
    match p.expandRefs with
    | .defs decls bodies main layers =>
      bodyDeps app holes decls decls bodies 0 [0] ++
        [⟨.main, [1], .part ⟨app, holes, .block decls⟩ [] main⟩] ++
        match layers with
        | .nil => []
        | .cons _ _ =>
          [⟨.layers, [2], .part ⟨app, holes, .block decls⟩ [] (Part.layersProgram layers)⟩]
    | expanded => [⟨.main, [], .part ⟨app, holes, .root⟩ [] expanded⟩]

def layerPath : List Nat → List Nat
  | 0 :: 0 :: rest => 2 :: rest
  | p => p

def layerRefusal (r : TypeRefusal) : TypeRefusal := Located.mapSite layerPath r

def layerTable (v : Verdict) : List Table.Entry :=
  v.table.filterMap fun e =>
    match e.path with
    | 0 :: 0 :: rest =>
      some ⟨2 :: rest, e.env, e.result.map fun r => r.mapError layerRefusal⟩
    | _ => none

def joinBodies : List DefDecl → Effs NativeOp → List Nat → List Verdict →
    Option (List Table.Entry × Except TypeRefusal Unit × List Verdict)
  | d :: ds, .cons _body rest, base, v :: vs => do
    let (tail, checked, unused) ← joinBodies ds rest (base ++ [1]) vs
    let placed := place (base ++ [0]) v
    let result : Except TypeRefusal Unit := do
      unless d.formed do throw ⟨base ++ [0], .definitionColumns d.name⟩
      let t ← placed.result
      unless d.admits t do throw ⟨base ++ [0], .bodyNotDeclared d.name t⟩
      checked
    pure (⟨base, none, none⟩ :: (placed.table ++ tail), result, unused)
  | [], .cons body rest, base, vs => do
    let (tail, _, unused) ← joinBodies [] rest (base ++ [1]) vs
    let bodyEntries := (Node.addresses (.eff body)).map fun p => ⟨base ++ 0 :: p, none, none⟩
    pure (⟨base, none, none⟩ :: (bodyEntries ++ tail), .ok (), unused)
  | _, .nil, base, vs => some ([⟨base, none, none⟩], .ok (), vs)
  | _ :: _, .cons _ _, _, [] => none

def joinModule (_app : SigApp) (holes : RowTable) (p : NativeEff)
    (vs : List Verdict) : Option Verdict := do
  let s : Sketch := ⟨p, holes⟩
  let (root, table) ←
    match p.expandRefs with
    | .defs decls bodies _main layers => do
      let (bodyTable, bodyResult, remaining) ← joinBodies decls bodies [0] vs
      match remaining with
      | mainVerdict :: rest =>
        let mainPlaced := place [1] mainVerdict
        let (layerResult, layerEntries) ←
          match layers, rest with
          | .nil, [] => some ((.ok () : Except TypeRefusal Unit), [⟨[2], none, none⟩])
          | .cons _ _, [v] => some (v.result.map (fun _ => ()) |>.mapError layerRefusal, layerTable v)
          | _, _ => none
        let root : Except TypeRefusal EffTy := do
          unless decls.length = bodies.toList.length do
            throw ⟨[], .definitionsMismatch decls.length bodies.toList.length⟩
          bodyResult
          let t ← mainPlaced.result
          layerResult
          pure t
        some (root, ⟨[], some (.env []), some root⟩ ::
          (bodyTable ++ (mainPlaced.table ++ layerEntries)))
      | [] => none
    | _ =>
      match vs with
      | [v] => some (v.result, v.table)
      | _ => none
  let sourceRoot := match p.firstRefFault with
    | some (site, target, why) => .error ⟨site, .referenceIllFormed target why⟩
    | none => root
  pure ⟨sourceRoot, Table.atSource s.sites p.firstRefFault table⟩

def combine (i : CheckInput) (vs : List Verdict) : Verdict :=
  if vs.length != (deps i).length then run i
  else match i with
    | .part .. => run i
    | .module app holes p =>
      match joinModule app holes p vs with
      | some v => v
      | none => run i



end Internal
open Internal

/-- A certified oracle: the only way a consumer checks. Its agreement field erases. -/
structure Oracle where
  ask : CheckInput → Verdict
  agrees : ∀ i, ask i = run i

def Oracle.uncached : Oracle := ⟨run, fun _ => rfl⟩

/-- **The oracle has one value up to equality.** So a memo or Incremental behind an oracle can
change cost and never an answer, for every consumer at once. -/
theorem Oracle.eq_uncached (o : Oracle) : o = Oracle.uncached := by
  cases o with
  | mk ask agrees =>
    have h : ask = run := funext agrees
    subst h
    rfl

/-- The consequence every consumer inherits, with no proof of its own. -/
theorem Oracle.transparent {α : Sort _} (f : Oracle → α) (o : Oracle) :
    f o = f Oracle.uncached := by
  rw [Oracle.eq_uncached o]

/-- The checks a computation asked, each with its answer, in order. -/
abbrev Trace := List (CheckInput × Verdict)

/-- Every entry is the uncached answer of its key. -/
def TraceValid (t : Trace) : Prop := ∀ p ∈ t, p.2 = run p.1

/-- A consumer's result with its trace: a writer over the certified oracle. The constructor is
private and the validity is a field, so the only traces are those `pure`, `bind` and `ask` build.
The generated OCaml interface keeps the whole package abstract; the trace feeds `Memo.learn` and
never a reply. -/
structure Checked (α : Type) where
  private mk ::
  value : α
  trace : Trace
  valid : TraceValid trace

namespace Checked

def pure' {α : Type} (a : α) : Checked α := ⟨a, [], fun _ h => nomatch h⟩

def bind' {α β : Type} (x : Checked α) (f : α → Checked β) : Checked β :=
  let next := f x.value
  ⟨next.value, x.trace ++ next.trace, fun p hp => by
    rcases List.mem_append.mp hp with h | h
    · exact x.valid p h
    · exact next.valid p h⟩

instance : Monad Checked where
  pure := pure'
  bind := bind'

/-- Record actual dependency requests and combine their answers; record one answer for a part. -/
def ask (o : Oracle) (i : CheckInput) : Checked Verdict :=
  match i with
  | .part .. => ⟨o.ask i, [(i, o.ask i)], fun p hp => by
      simp only [List.mem_singleton] at hp
      subst hp
      exact o.agrees i⟩
  | .module .. =>
    let trace := (deps i).map (fun d => (d.input, o.ask d.input))
    ⟨combine i (trace.map Prod.snd), trace, fun p hp => by
      obtain ⟨d, _hd, he⟩ := List.mem_map.mp hp
      subst p
      exact o.agrees d.input⟩



end Checked

/-- The learning memo, in-process only. The constructor is private and the validity is a field:
the only memos are `empty` and what `learn` builds from `Checked` traces. Nothing imports
entries, so no call site is trusted; in OCaml the memo's trust is the generated code's, the
existing lowering boundary. -/
structure Memo where
  private mk ::
  entries : Trace
  valid : TraceValid entries

def Memo.empty : Memo := ⟨[], fun _ h => nomatch h⟩

def Memo.learn {α : Type} (m : Memo) (c : Checked α) : Memo :=
  ⟨c.trace ++ m.entries, fun p hp => by
    rcases List.mem_append.mp hp with h | h
    · exact c.valid p h
    · exact m.valid p h⟩

/-- When an entry may answer an asked key. A rule is sound when a valid entry it selects is the
uncached answer of the asked key; the oracle's agreement then follows for every memo. -/
structure HitRule where
  hit : CheckInput → CheckInput × Verdict → Bool
  sound : ∀ i e, hit i e = true → e.2 = run e.1 → e.2 = run i

/-- An exact hit: the entry's key is the asked key. -/
def HitRule.exact : HitRule where
  hit i e := decide (e.1 = i)
  sound i e h he := by
    have hk : e.1 = i := of_decide_eq_true h
    rw [he, hk]

/-- Either rule. -/
def HitRule.or (r s : HitRule) : HitRule where
  hit i e := r.hit i e || s.hit i e
  sound i e h he := by
    simp only [Bool.or_eq_true] at h
    cases h with
    | inl h => exact r.sound i e h he
    | inr h => exact s.sound i e h he

def extensionHit (i : CheckInput) (e : CheckInput × Verdict) : Bool :=
  match i, e.1 with
  | .part newer env p, .part older oldEnv oldP =>
      decide (oldP = p) && decide (oldEnv = env) && older.extendsB newer &&
        e.2.result.toBool && supportB older.signature oldP
  | _, _ => false

def extension : HitRule where
  hit := extensionHit
  sound := by
    intro i e hh hv
    obtain ⟨old, verdict⟩ := e
    cases i with
    | module app holes p =>
      cases old <;> cases hh
    | part newer env p =>
      cases old with
      | module app holes q => cases hh
      | part older oldEnv oldP =>
        simp only [extensionHit, Bool.and_eq_true, decide_eq_true_eq] at hh
        obtain ⟨⟨⟨⟨hq, henv⟩, he⟩, _positive⟩, hs⟩ := hh
        subst oldP
        subst oldEnv
        exact hv.trans (congrArg (fun out : List Table.Entry × Except TypeRefusal EffTy =>
          (⟨out.2, out.1⟩ : Verdict)) (guarded_extends p env he hs))




/-- A memo-backed oracle under a sound hit rule: a hit, else `run`. -/
def Memo.oracle (m : Memo) (r : HitRule) : Oracle where
  ask i := match m.entries.find? (r.hit i) with
    | some e => e.2
    | none => run i
  agrees i := by
    show (match m.entries.find? (r.hit i) with
      | some e => e.2
      | none => run i) = run i
    split
    · rename_i e he
      exact r.sound i e (List.find?_some (p := r.hit i) he)
        (m.valid e (List.mem_of_find?_eq_some he))
    · rfl


/-- The native export of the existing value projection. -/
def Checked.readVerdict (c : Checked Verdict) : Verdict := c.value

inductive Site where
  | address (path : List Nat)
  | inCopy (site path : List Nat)
  | column (at_ : List Nat)
  | application

structure Explanation where
  refusal : TypeRefusal
  site : Site
  part : Option CheckInput

def locatedResult (d : Dep) (v : Verdict) : Except TypeRefusal EffTy :=
  match d.role with
  | .layers => v.result.mapError layerRefusal
  | _ => (place d.base v).result

def refusalSite (i : CheckInput) (why : TypeRefusal) : Site :=
  match i with
  | .part .. => .address why.path
  | .module _ _ p =>
    match (p.refSites []).find? (fun site => site.1.isPrefixOf why.path && decide (site.1 ≠ why.path)) with
    | some (site,_) => .inCopy site why.path
    | none =>
      match why.reason with
      | .definitionColumns _ => .column why.path
      | _ => .address why.path

/-- Explain an actual answer. Only an actual local refusal populates part. -/
def explain (o : Oracle) (i : CheckInput) : Checked (Option Explanation) :=
  let checked := Checked.ask o i
  checked.bind' fun verdict => pure <|
    match verdict.result with
    | .ok _ => none
    | .error why =>
      let localPart := match i with
        | .part .. => some i
        | .module .. =>
          (((deps i).zip checked.trace).find? (fun (d,e) =>
            decide (locatedResult d e.2 = .error why))).map (fun (d,_) => d.input)
      some ⟨why,refusalSite i why,localPart⟩

end Check
end Effect4.Program
