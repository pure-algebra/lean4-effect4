import Effect4.Program.Native
import Cas.Canonical

/-!
# Cas.Program

Owner: the canonical instances of the program syntax, `Eff NativeOp` and the family under it —
the stretch item of lane S1.

`src/Effect4/Program/Wire.lean` writes a program as constructor frames (`ctor i args := framed
Tag.ctor (encode i ++ args.flatten)`, `Wire.lean:35-36`) with the constructor indices in
declaration order, a structure as constructor 0 with its fields in declaration order, and the
mutual list types as `nil = 0`, `cons = 1`. The `toVal`s below write the same tree, so
`Canonical.encode` is the Wire's `encodeProgram` byte for byte; the eight corpus programs
(`Wire.lean:576-618`, copied here) are guarded against the goldens under `ocaml/goldens/eff`,
and `p42`'s digest is the facts note's `fa5f40…62a3`.

The Wire's owed theorems — round trip and exactness — are the instances' fields. Every
alphabet without recursion (`Lit`, `FnName`, `FinalizerStrategy`, `MaskMode`, `ObserverMode`,
`NativeOp`, `ForkOptions`) reads structurally with the template scripts; every recursive
family (`Term`/`Terms`, `CauseTerm`, the five-type `Eff` block) reads through
`guarded toVal raw`: the structural reader `raw` is a left inverse (`raw_toVal`, one mutual
structural induction), and the guard makes it exact. The string frames decode through
`decodeString`, so the Wire's own re-encode guard on strings (`Wire.lean:254-262`) is gone
from the byte layer; the guard here is on trees.

Shapes compose through the class: a field of type `F` contributes `(shape F).root` to the
fields and `(shape F).defs` to the table; a mutual block shares one table and refers to its
members by `named`. `Option Term` is the derived `Canonical (Option Term)`, so `interrupt none`
frames as `none` (tag 6) and `interrupt (some t)` as `some` (tag 7), the Wire's `encOptTerm`.
-/

set_option autoImplicit false

namespace Effect4.Store

open Effect4 (FinalizerStrategy)
open Effect4.Machine (FnName)
open Effect4.Supervision (ForkOptions MaskMode ObserverMode)
open Effect4.Program (Lit Term Terms CauseTerm Eff Stmt Stmts Effs ActionTerm NativeOp)

namespace ProgramCanonical

/-! ## The literal alphabet -/

namespace LitC

def shapeDoc : ShapeDoc :=
  ⟨.sum "Lit"
    [("unit", []), ("nat", [("value", (shape Nat).root)]), ("bool", [("value", (shape Bool).root)]),
     ("str", [("value", (shape String).root)])], []⟩

def toVal : Lit → Val
  | .unit => .ctor 0 []
  | .nat n => .ctor 1 [Canonical.toVal n]
  | .bool b => .ctor 2 [Canonical.toVal b]
  | .str s => .ctor 3 [Canonical.toVal s]

def ofVal : Val → Option Lit
  | .ctor 0 [] => some .unit
  | .ctor 1 [v] => (Canonical.ofVal (α := Nat) v).map .nat
  | .ctor 2 [v] => (Canonical.ofVal (α := Bool) v).map .bool
  | .ctor 3 [v] => (Canonical.ofVal (α := String) v).map .str
  | _ => none

theorem ofVal_toVal (a : Lit) : ofVal (toVal a) = some a := by
  cases a <;> simp [toVal, ofVal, Canonical.ofVal_toVal]

theorem ofVal_exact {v : Val} {a : Lit} (h : ofVal v = some a) : v = toVal a := by
  unfold ofVal at h
  split at h
  all_goals first
    | (injection h with h; subst h; rfl)
    | (rename_i w
       obtain ⟨x, hx, hj⟩ := Option.map_eq_some_iff.mp h
       subst hj
       simp only [toVal]
       rw [Canonical.ofVal_exact hx])
    | exact nomatch h

theorem fits (a : Lit) : shapeDoc.accepts (toVal a) = true := by
  cases a with
  | unit => exact accepts_sum _ _ _ 0 "unit" [] [] rfl (acceptsFields_nil _)
  | nat n =>
    exact accepts_sum _ _ _ 1 "nat" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (Canonical.fits n) (acceptsFields_nil _))
  | bool b =>
    exact accepts_sum _ _ _ 2 "bool" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (Canonical.fits b) (acceptsFields_nil _))
  | str s =>
    exact accepts_sum _ _ _ 3 "str" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (Canonical.fits s) (acceptsFields_nil _))

instance instCanonical : Canonical Lit := ⟨shapeDoc, toVal, ofVal, ofVal_toVal, ofVal_exact, fits⟩

end LitC

/-! ## The nullary alphabets -/

namespace FnNameC

def shapeDoc : ShapeDoc :=
  ⟨.sum "FnName"
    [("incr", []), ("double", []), ("zeroWhenPositive", []), ("noChange", []),
     ("takeAndBump", [])], []⟩

def toVal : FnName → Val
  | .incr => .ctor 0 []
  | .double => .ctor 1 []
  | .zeroWhenPositive => .ctor 2 []
  | .noChange => .ctor 3 []
  | .takeAndBump => .ctor 4 []

def ofVal : Val → Option FnName
  | .ctor 0 [] => some .incr
  | .ctor 1 [] => some .double
  | .ctor 2 [] => some .zeroWhenPositive
  | .ctor 3 [] => some .noChange
  | .ctor 4 [] => some .takeAndBump
  | _ => none

theorem ofVal_toVal (a : FnName) : ofVal (toVal a) = some a := by cases a <;> rfl

theorem ofVal_exact {v : Val} {a : FnName} (h : ofVal v = some a) : v = toVal a := by
  unfold ofVal at h
  split at h
  all_goals first
    | (injection h with h; subst h; rfl)
    | exact nomatch h

theorem fits (a : FnName) : shapeDoc.accepts (toVal a) = true := by cases a <;> decide

instance instCanonical : Canonical FnName :=
  ⟨shapeDoc, toVal, ofVal, ofVal_toVal, ofVal_exact, fits⟩

end FnNameC

namespace StrategyC

def shapeDoc : ShapeDoc := ⟨.sum "FinalizerStrategy" [("sequential", []), ("parallel", [])], []⟩

def toVal : FinalizerStrategy → Val
  | .sequential => .ctor 0 []
  | .parallel => .ctor 1 []

def ofVal : Val → Option FinalizerStrategy
  | .ctor 0 [] => some .sequential
  | .ctor 1 [] => some .parallel
  | _ => none

theorem ofVal_toVal (a : FinalizerStrategy) : ofVal (toVal a) = some a := by cases a <;> rfl

theorem ofVal_exact {v : Val} {a : FinalizerStrategy} (h : ofVal v = some a) : v = toVal a := by
  unfold ofVal at h
  split at h
  all_goals first
    | (injection h with h; subst h; rfl)
    | exact nomatch h

theorem fits (a : FinalizerStrategy) : shapeDoc.accepts (toVal a) = true := by cases a <;> decide

instance instCanonical : Canonical FinalizerStrategy :=
  ⟨shapeDoc, toVal, ofVal, ofVal_toVal, ofVal_exact, fits⟩

end StrategyC

namespace MaskModeC

def shapeDoc : ShapeDoc :=
  ⟨.sum "MaskMode" [("interruptible", []), ("uninterruptible", []), ("inherit", [])], []⟩

def toVal : MaskMode → Val
  | .interruptible => .ctor 0 []
  | .uninterruptible => .ctor 1 []
  | .inherit => .ctor 2 []

def ofVal : Val → Option MaskMode
  | .ctor 0 [] => some .interruptible
  | .ctor 1 [] => some .uninterruptible
  | .ctor 2 [] => some .inherit
  | _ => none

theorem ofVal_toVal (a : MaskMode) : ofVal (toVal a) = some a := by cases a <;> rfl

theorem ofVal_exact {v : Val} {a : MaskMode} (h : ofVal v = some a) : v = toVal a := by
  unfold ofVal at h
  split at h
  all_goals first
    | (injection h with h; subst h; rfl)
    | exact nomatch h

theorem fits (a : MaskMode) : shapeDoc.accepts (toVal a) = true := by cases a <;> decide

instance instCanonical : Canonical MaskMode :=
  ⟨shapeDoc, toVal, ofVal, ofVal_toVal, ofVal_exact, fits⟩

end MaskModeC

namespace ObserverModeC

def shapeDoc : ShapeDoc := ⟨.sum "ObserverMode" [("awaitValue", []), ("joinEffect", [])], []⟩

def toVal : ObserverMode → Val
  | .awaitValue => .ctor 0 []
  | .joinEffect => .ctor 1 []

def ofVal : Val → Option ObserverMode
  | .ctor 0 [] => some .awaitValue
  | .ctor 1 [] => some .joinEffect
  | _ => none

theorem ofVal_toVal (a : ObserverMode) : ofVal (toVal a) = some a := by cases a <;> rfl

theorem ofVal_exact {v : Val} {a : ObserverMode} (h : ofVal v = some a) : v = toVal a := by
  unfold ofVal at h
  split at h
  all_goals first
    | (injection h with h; subst h; rfl)
    | exact nomatch h

theorem fits (a : ObserverMode) : shapeDoc.accepts (toVal a) = true := by cases a <;> decide

instance instCanonical : Canonical ObserverMode :=
  ⟨shapeDoc, toVal, ofVal, ofVal_toVal, ofVal_exact, fits⟩

end ObserverModeC

/-! ## The native operations -/

namespace NativeOpC

def shapeDoc : ShapeDoc :=
  ⟨.sum "NativeOp"
    [("refMake", []), ("refGet", []), ("refSet", []), ("refGetAndSet", []), ("refSetAndGet", []),
     ("refUpdate", [("f", (shape FnName).root)]), ("refGetAndUpdate", [("f", (shape FnName).root)]),
     ("refUpdateAndGet", [("f", (shape FnName).root)]), ("refUpdateSome", [("f", (shape FnName).root)]),
     ("refGetAndUpdateSome", [("f", (shape FnName).root)]),
     ("refUpdateSomeAndGet", [("f", (shape FnName).root)]), ("refModify", [("f", (shape FnName).root)]),
     ("refModifySome", [("f", (shape FnName).root)]), ("deferredMake", []), ("deferredIsDone", []),
     ("deferredPoll", []), ("deferredSucceed", []), ("deferredFail", []), ("deferredAwait", []),
     ("scopeMake", [("strategy", (shape FinalizerStrategy).root)])],
   (shape FnName).defs ++ (shape FinalizerStrategy).defs⟩

def toVal : NativeOp → Val
  | .refMake => .ctor 0 []
  | .refGet => .ctor 1 []
  | .refSet => .ctor 2 []
  | .refGetAndSet => .ctor 3 []
  | .refSetAndGet => .ctor 4 []
  | .refUpdate f => .ctor 5 [Canonical.toVal f]
  | .refGetAndUpdate f => .ctor 6 [Canonical.toVal f]
  | .refUpdateAndGet f => .ctor 7 [Canonical.toVal f]
  | .refUpdateSome f => .ctor 8 [Canonical.toVal f]
  | .refGetAndUpdateSome f => .ctor 9 [Canonical.toVal f]
  | .refUpdateSomeAndGet f => .ctor 10 [Canonical.toVal f]
  | .refModify f => .ctor 11 [Canonical.toVal f]
  | .refModifySome f => .ctor 12 [Canonical.toVal f]
  | .deferredMake => .ctor 13 []
  | .deferredIsDone => .ctor 14 []
  | .deferredPoll => .ctor 15 []
  | .deferredSucceed => .ctor 16 []
  | .deferredFail => .ctor 17 []
  | .deferredAwait => .ctor 18 []
  | .scopeMake s => .ctor 19 [Canonical.toVal s]

def ofVal : Val → Option NativeOp
  | .ctor 0 [] => some .refMake
  | .ctor 1 [] => some .refGet
  | .ctor 2 [] => some .refSet
  | .ctor 3 [] => some .refGetAndSet
  | .ctor 4 [] => some .refSetAndGet
  | .ctor 5 [v] => (Canonical.ofVal (α := FnName) v).map .refUpdate
  | .ctor 6 [v] => (Canonical.ofVal (α := FnName) v).map .refGetAndUpdate
  | .ctor 7 [v] => (Canonical.ofVal (α := FnName) v).map .refUpdateAndGet
  | .ctor 8 [v] => (Canonical.ofVal (α := FnName) v).map .refUpdateSome
  | .ctor 9 [v] => (Canonical.ofVal (α := FnName) v).map .refGetAndUpdateSome
  | .ctor 10 [v] => (Canonical.ofVal (α := FnName) v).map .refUpdateSomeAndGet
  | .ctor 11 [v] => (Canonical.ofVal (α := FnName) v).map .refModify
  | .ctor 12 [v] => (Canonical.ofVal (α := FnName) v).map .refModifySome
  | .ctor 13 [] => some .deferredMake
  | .ctor 14 [] => some .deferredIsDone
  | .ctor 15 [] => some .deferredPoll
  | .ctor 16 [] => some .deferredSucceed
  | .ctor 17 [] => some .deferredFail
  | .ctor 18 [] => some .deferredAwait
  | .ctor 19 [v] => (Canonical.ofVal (α := FinalizerStrategy) v).map .scopeMake
  | _ => none

theorem ofVal_toVal (a : NativeOp) : ofVal (toVal a) = some a := by
  cases a <;> simp [toVal, ofVal, Canonical.ofVal_toVal]

theorem ofVal_exact {v : Val} {a : NativeOp} (h : ofVal v = some a) : v = toVal a := by
  unfold ofVal at h
  split at h
  all_goals first
    | (injection h with h; subst h; rfl)
    | (rename_i w
       obtain ⟨x, hx, hj⟩ := Option.map_eq_some_iff.mp h
       subst hj
       simp only [toVal]
       rw [Canonical.ofVal_exact hx])
    | exact nomatch h

theorem fits (a : NativeOp) : shapeDoc.accepts (toVal a) = true := by
  cases a
  all_goals first
    | decide
    | (rename_i x; cases x <;> decide)

instance instCanonical : Canonical NativeOp :=
  ⟨shapeDoc, toVal, ofVal, ofVal_toVal, ofVal_exact, fits⟩

end NativeOpC

/-! ## The fork options -/

namespace ForkOptionsC

def shapeDoc : ShapeDoc :=
  ⟨.struct "ForkOptions"
    [("startImmediately", (shape Bool).root), ("daemon", (shape Bool).root),
     ("maskMode", (shape MaskMode).root)],
   (shape Bool).defs ++ (shape Bool).defs ++ (shape MaskMode).defs⟩

def toVal (o : ForkOptions) : Val :=
  .ctor 0 [Canonical.toVal o.startImmediately, Canonical.toVal o.daemon, Canonical.toVal o.maskMode]

def ofVal : Val → Option ForkOptions
  | .ctor 0 [s, d, m] =>
    match Canonical.ofVal (α := Bool) s, Canonical.ofVal (α := Bool) d,
        Canonical.ofVal (α := MaskMode) m with
    | some s, some d, some m => some ⟨s, d, m⟩
    | _, _, _ => none
  | _ => none

theorem ofVal_toVal (o : ForkOptions) : ofVal (toVal o) = some o := by
  obtain ⟨s, d, m⟩ := o
  simp [toVal, ofVal, Canonical.ofVal_toVal]

theorem ofVal_exact {v : Val} {o : ForkOptions} (h : ofVal v = some o) : v = toVal o := by
  unfold ofVal at h
  split at h
  · next s d m =>
    split at h
    · next s' d' m' hs hd hm =>
      injection h with h
      subst h
      simp only [toVal]
      rw [Canonical.ofVal_exact hs, Canonical.ofVal_exact hd, Canonical.ofVal_exact hm]
    · exact nomatch h
  · exact nomatch h

theorem fits (o : ForkOptions) : shapeDoc.accepts (toVal o) = true := by
  obtain ⟨s, d, m⟩ := o
  apply accepts_struct
  exact acceptsFields_cons _ _ _ _ _ _ (Canonical.fits s) (acceptsFields_cons _ _ _ _ _ _
    (Canonical.fits d) (acceptsFields_cons _ _ _ _ _ _ (Canonical.fits m) (acceptsFields_nil _)))

instance instCanonical : Canonical ForkOptions :=
  ⟨shapeDoc, toVal, ofVal, ofVal_toVal, ofVal_exact, fits⟩

end ForkOptionsC

/-! ## Terms, a mutual pair -/

namespace TermC

def termShape : Shape :=
  .sum "Term"
    [("var", [("index", (shape Nat).root)]), ("lit", [("value", (shape Lit).root)]),
     ("app", [("atom", (shape String).root), ("args", .named "Terms")])]

def termsShape : Shape :=
  .sum "Terms" [("nil", []), ("cons", [("head", .named "Term"), ("tail", .named "Terms")])]

def defs : List (String × Shape) :=
  ("Term", termShape) :: ("Terms", termsShape) ::
    ((shape Nat).defs ++ (shape Lit).defs ++ (shape String).defs)

mutual
def toValT : Term → Val
  | .var i => .ctor 0 [Canonical.toVal i]
  | .lit l => .ctor 1 [Canonical.toVal l]
  | .app atom args => .ctor 2 [Canonical.toVal atom, toValTs args]
def toValTs : Terms → Val
  | .nil => .ctor 0 []
  | .cons h t => .ctor 1 [toValT h, toValTs t]
end

mutual
def rawT : Val → Option Term
  | .ctor 0 [i] => (Canonical.ofVal (α := Nat) i).map .var
  | .ctor 1 [l] => (Canonical.ofVal (α := Lit) l).map .lit
  | .ctor 2 [a, ts] =>
    match Canonical.ofVal (α := String) a, rawTs ts with
    | some a, some ts => some (.app a ts)
    | _, _ => none
  | _ => none
def rawTs : Val → Option Terms
  | .ctor 0 [] => some .nil
  | .ctor 1 [h, t] =>
    match rawT h, rawTs t with
    | some h, some t => some (.cons h t)
    | _, _ => none
  | _ => none
end

mutual
theorem rawT_toValT (t : Term) : rawT (toValT t) = some t := by
  cases t with
  | var i => simp [toValT, rawT, Canonical.ofVal_toVal]
  | lit l => simp [toValT, rawT, Canonical.ofVal_toVal]
  | app a args => simp [toValT, rawT, Canonical.ofVal_toVal, rawTs_toValTs args]
termination_by structural t
theorem rawTs_toValTs (ts : Terms) : rawTs (toValTs ts) = some ts := by
  cases ts with
  | nil => rfl
  | cons h t => simp [toValTs, rawTs, rawT_toValT h, rawTs_toValTs t]
termination_by structural ts
end

theorem mem_term : ("Term", termShape) ∈ defs := List.Mem.head _
theorem mem_terms : ("Terms", termsShape) ∈ defs := List.Mem.tail _ (List.Mem.head _)

theorem lift_nat (n : Nat) : acceptsIn defs (shape Nat).root (Canonical.toVal n) = true :=
  acceptsIn_mono_of_subset
    (fun _ hp => List.Mem.tail _ (List.Mem.tail _ (mem_append_of_left (mem_append_of_left hp))))
    _ _ (Canonical.fits n)

theorem lift_lit (l : Lit) : acceptsIn defs (shape Lit).root (Canonical.toVal l) = true :=
  acceptsIn_mono_of_subset
    (fun _ hp => List.Mem.tail _ (List.Mem.tail _ (mem_append_of_left (mem_append_of_right hp))))
    _ _ (Canonical.fits l)

theorem lift_string (s : String) : acceptsIn defs (shape String).root (Canonical.toVal s) = true :=
  acceptsIn_mono_of_subset
    (fun _ hp => List.Mem.tail _ (List.Mem.tail _ (mem_append_of_right hp)))
    _ _ (Canonical.fits s)

mutual
theorem fitsT (t : Term) : acceptsIn defs (.named "Term") (toValT t) = true := by
  apply accepts_named_of_mem _ _ termShape _ mem_term
  cases t with
  | var i =>
    exact acceptsAt_sum _ _ _ 0 "var" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (lift_nat i) (acceptsFields_nil _))
  | lit l =>
    exact acceptsAt_sum _ _ _ 1 "lit" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (lift_lit l) (acceptsFields_nil _))
  | app a args =>
    exact acceptsAt_sum _ _ _ 2 "app" _ _ rfl (acceptsFields_cons _ _ _ _ _ _ (lift_string a)
      (acceptsFields_cons _ _ _ _ _ _ (fitsTs args) (acceptsFields_nil _)))
termination_by structural t
theorem fitsTs (ts : Terms) : acceptsIn defs (.named "Terms") (toValTs ts) = true := by
  apply accepts_named_of_mem _ _ termsShape _ mem_terms
  cases ts with
  | nil => exact acceptsAt_sum _ _ _ 0 "nil" [] [] rfl (acceptsFields_nil _)
  | cons h t =>
    exact acceptsAt_sum _ _ _ 1 "cons" _ _ rfl (acceptsFields_cons _ _ _ _ _ _ (fitsT h)
      (acceptsFields_cons _ _ _ _ _ _ (fitsTs t) (acceptsFields_nil _)))
termination_by structural ts
end

instance instCanonicalTerm : Canonical Term :=
  ⟨⟨.named "Term", defs⟩, toValT, guarded toValT rawT,
    fun t => guarded_toVal _ _ t (rawT_toValT t), fun h => guarded_exact h, fitsT⟩

instance instCanonicalTerms : Canonical Terms :=
  ⟨⟨.named "Terms", defs⟩, toValTs, guarded toValTs rawTs,
    fun ts => guarded_toVal _ _ ts (rawTs_toValTs ts), fun h => guarded_exact h, fitsTs⟩

end TermC

/-! ## Causes -/

namespace CauseC

def causeShape : Shape :=
  .sum "CauseTerm"
    [("fail", [("error", (shape Term).root)]), ("die", [("defect", (shape Term).root)]),
     ("interrupt", [("interruptor", (shape (Option Term)).root)]),
     ("both", [("left", .named "CauseTerm"), ("right", .named "CauseTerm")])]

def defs : List (String × Shape) :=
  ("CauseTerm", causeShape) :: ((shape Term).defs ++ (shape (Option Term)).defs)

def toVal : CauseTerm → Val
  | .fail e => .ctor 0 [Canonical.toVal e]
  | .die d => .ctor 1 [Canonical.toVal d]
  | .interrupt o => .ctor 2 [Canonical.toVal o]
  | .both l r => .ctor 3 [toVal l, toVal r]

def raw : Val → Option CauseTerm
  | .ctor 0 [e] => (Canonical.ofVal (α := Term) e).map .fail
  | .ctor 1 [d] => (Canonical.ofVal (α := Term) d).map .die
  | .ctor 2 [o] => (Canonical.ofVal (α := Option Term) o).map .interrupt
  | .ctor 3 [l, r] =>
    match raw l, raw r with
    | some l, some r => some (.both l r)
    | _, _ => none
  | _ => none

theorem raw_toVal (c : CauseTerm) : raw (toVal c) = some c := by
  induction c with
  | fail e => simp [toVal, raw, Canonical.ofVal_toVal]
  | die d => simp [toVal, raw, Canonical.ofVal_toVal]
  | interrupt o => simp [toVal, raw, Canonical.ofVal_toVal]
  | both l r ihl ihr => simp [toVal, raw, ihl, ihr]

theorem mem_cause : ("CauseTerm", causeShape) ∈ defs := List.Mem.head _

theorem lift_term (t : Term) : acceptsIn defs (shape Term).root (Canonical.toVal t) = true :=
  acceptsIn_mono_of_subset (fun _ hp => List.Mem.tail _ (mem_append_of_left hp)) _ _
    (Canonical.fits t)

theorem lift_opt (o : Option Term) :
    acceptsIn defs (shape (Option Term)).root (Canonical.toVal o) = true :=
  acceptsIn_mono_of_subset (fun _ hp => List.Mem.tail _ (mem_append_of_right hp)) _ _
    (Canonical.fits o)

theorem fits (c : CauseTerm) : acceptsIn defs (.named "CauseTerm") (toVal c) = true := by
  induction c with
  | fail e =>
    exact accepts_named_of_mem _ _ causeShape _ mem_cause (acceptsAt_sum _ _ _ 0 "fail" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (lift_term e) (acceptsFields_nil _)))
  | die d =>
    exact accepts_named_of_mem _ _ causeShape _ mem_cause (acceptsAt_sum _ _ _ 1 "die" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (lift_term d) (acceptsFields_nil _)))
  | interrupt o =>
    exact accepts_named_of_mem _ _ causeShape _ mem_cause
      (acceptsAt_sum _ _ _ 2 "interrupt" _ _ rfl
        (acceptsFields_cons _ _ _ _ _ _ (lift_opt o) (acceptsFields_nil _)))
  | both l r ihl ihr =>
    exact accepts_named_of_mem _ _ causeShape _ mem_cause (acceptsAt_sum _ _ _ 3 "both" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ ihl (acceptsFields_cons _ _ _ _ _ _ ihr (acceptsFields_nil _))))

instance instCanonical : Canonical CauseTerm :=
  ⟨⟨.named "CauseTerm", defs⟩, toVal, guarded toVal raw,
    fun c => guarded_toVal _ _ c (raw_toVal c), fun h => guarded_exact h, fits⟩

end CauseC

/-! ## The program block: five mutual types -/

namespace EffC

/-- The field shapes of the block, as the generator would spell them: a member of the block by
name, any other type by its instance's root. -/
def T : Shape := (shape Term).root
def E : Shape := .named "Eff"

def effShape : Shape :=
  .sum "Eff"
    [("succeed", [("value", T)]),
     ("fail", [("error", T)]),
     ("failCause", [("cause", (shape CauseTerm).root)]),
     ("yieldError", [("error", T)]),
     ("sync", [("thunk", T)]),
     ("suspend", [("body", E)]),
     ("perform", [("op", (shape NativeOp).root), ("request", T)]),
     ("bind", [("first", E), ("rest", E)]),
     ("gen", [("body", .named "Stmts")]),
     ("catchCause", [("body", E), ("handler", E)]),
     ("matchCause", [("body", E), ("onValue", E), ("onCause", E)]),
     ("onExit", [("body", E), ("finalizer", E)]),
     ("exit", [("body", E)]),
     ("uninterruptible", [("body", E)]),
     ("interruptible", [("body", E)]),
     ("branch", [("test", T), ("thenB", E), ("elseB", E)]),
     ("whileLoop", [("initial", T), ("test", T), ("step", T), ("body", E)]),
     ("yieldNow", [("priority", (shape Nat).root)]),
     ("callback", [("register", (shape NativeOp).root), ("request", T)]),
     ("awaitFiber", [("fiber", T), ("mode", (shape ObserverMode).root)]),
     ("withFiber", [("action", .named "ActionTerm")]),
     ("scoped", [("body", E)]),
     ("acquireRelease", [("acquire", E), ("release", E)]),
     ("choose", [("site", (shape Nat).root), ("left", E), ("right", E)])]

def stmtShape : Shape :=
  .sum "Stmt"
    [("bindYield", [("effect", E)]),
     ("yieldDiscard", [("effect", E)]),
     ("ret", [("value", T)]),
     ("ifElse", [("test", T), ("thenB", .named "Stmts"), ("elseB", .named "Stmts")]),
     ("whileTrue", [("body", .named "Stmts")]),
     ("breakLoop", [])]

def stmtsShape : Shape :=
  .sum "Stmts" [("nil", []), ("cons", [("head", .named "Stmt"), ("tail", .named "Stmts")])]

def effsShape : Shape :=
  .sum "Effs" [("nil", []), ("cons", [("head", E), ("tail", .named "Effs")])]

def actionShape : Shape :=
  .sum "ActionTerm"
    [("fork", [("program", E), ("options", (shape ForkOptions).root)]),
     ("forkIn", [("program", E), ("options", (shape ForkOptions).root), ("scope", T)]),
     ("forkScoped", [("program", E), ("options", (shape ForkOptions).root)]),
     ("runIn", [("target", T), ("scope", T)]),
     ("interrupt", [("target", T)]),
     ("interruptScoped", [("target", T)]),
     ("interruptAll", [("targets", T), ("interruptor", (shape (Option Term)).root)]),
     ("awaitAll", [("targets", T)]),
     ("awaitAllFailFast", [("targets", T)]),
     ("snapshotChildren", []),
     ("awaitNewChildren", [("snapshot", T)]),
     ("raceAll", [("entrants", .named "Effs")]),
     ("setContext", [("context", T)]),
     ("getContext", []),
     ("getId", []),
     ("closeScope", [("scope", T), ("exit", T)])]

/-- One table for the block, then the field types' tables. -/
def defs : List (String × Shape) :=
  ("Eff", effShape) :: ("Stmt", stmtShape) :: ("Stmts", stmtsShape) :: ("Effs", effsShape) ::
    ("ActionTerm", actionShape) ::
    ((shape Term).defs ++ (shape CauseTerm).defs ++ (shape NativeOp).defs ++ (shape Nat).defs ++
      (shape ObserverMode).defs ++ (shape ForkOptions).defs ++ (shape (Option Term)).defs)

mutual
def toValEff : Eff NativeOp → Val
  | .succeed v => .ctor 0 [Canonical.toVal v]
  | .fail e => .ctor 1 [Canonical.toVal e]
  | .failCause c => .ctor 2 [Canonical.toVal c]
  | .yieldError e => .ctor 3 [Canonical.toVal e]
  | .sync t => .ctor 4 [Canonical.toVal t]
  | .suspend b => .ctor 5 [toValEff b]
  | .perform op r => .ctor 6 [Canonical.toVal op, Canonical.toVal r]
  | .bind a b => .ctor 7 [toValEff a, toValEff b]
  | .gen body => .ctor 8 [toValStmts body]
  | .catchCause b h => .ctor 9 [toValEff b, toValEff h]
  | .matchCause b v c => .ctor 10 [toValEff b, toValEff v, toValEff c]
  | .onExit b f => .ctor 11 [toValEff b, toValEff f]
  | .exit b => .ctor 12 [toValEff b]
  | .uninterruptible b => .ctor 13 [toValEff b]
  | .interruptible b => .ctor 14 [toValEff b]
  | .branch t a b => .ctor 15 [Canonical.toVal t, toValEff a, toValEff b]
  | .whileLoop i t s b => .ctor 16 [Canonical.toVal i, Canonical.toVal t, Canonical.toVal s, toValEff b]
  | .yieldNow p => .ctor 17 [Canonical.toVal p]
  | .callback reg r => .ctor 18 [Canonical.toVal reg, Canonical.toVal r]
  | .awaitFiber f m => .ctor 19 [Canonical.toVal f, Canonical.toVal m]
  | .withFiber a => .ctor 20 [toValAction a]
  | .scoped b => .ctor 21 [toValEff b]
  | .acquireRelease a r => .ctor 22 [toValEff a, toValEff r]
  | .choose site l r => .ctor 23 [Canonical.toVal site, toValEff l, toValEff r]
def toValStmt : Stmt NativeOp → Val
  | .bindYield e => .ctor 0 [toValEff e]
  | .yieldDiscard e => .ctor 1 [toValEff e]
  | .ret v => .ctor 2 [Canonical.toVal v]
  | .ifElse t a b => .ctor 3 [Canonical.toVal t, toValStmts a, toValStmts b]
  | .whileTrue b => .ctor 4 [toValStmts b]
  | .breakLoop => .ctor 5 []
def toValStmts : Stmts NativeOp → Val
  | .nil => .ctor 0 []
  | .cons h t => .ctor 1 [toValStmt h, toValStmts t]
def toValEffs : Effs NativeOp → Val
  | .nil => .ctor 0 []
  | .cons h t => .ctor 1 [toValEff h, toValEffs t]
def toValAction : ActionTerm NativeOp → Val
  | .fork p o => .ctor 0 [toValEff p, Canonical.toVal o]
  | .forkIn p o s => .ctor 1 [toValEff p, Canonical.toVal o, Canonical.toVal s]
  | .forkScoped p o => .ctor 2 [toValEff p, Canonical.toVal o]
  | .runIn t s => .ctor 3 [Canonical.toVal t, Canonical.toVal s]
  | .interrupt t => .ctor 4 [Canonical.toVal t]
  | .interruptScoped t => .ctor 5 [Canonical.toVal t]
  | .interruptAll t i => .ctor 6 [Canonical.toVal t, Canonical.toVal i]
  | .awaitAll t => .ctor 7 [Canonical.toVal t]
  | .awaitAllFailFast t => .ctor 8 [Canonical.toVal t]
  | .snapshotChildren => .ctor 9 []
  | .awaitNewChildren s => .ctor 10 [Canonical.toVal s]
  | .raceAll es => .ctor 11 [toValEffs es]
  | .setContext c => .ctor 12 [Canonical.toVal c]
  | .getContext => .ctor 13 []
  | .getId => .ctor 14 []
  | .closeScope s e => .ctor 15 [Canonical.toVal s, Canonical.toVal e]
end

mutual
def rawEff : Val → Option (Eff NativeOp)
  | .ctor 0 [v] => (Canonical.ofVal (α := Term) v).map .succeed
  | .ctor 1 [v] => (Canonical.ofVal (α := Term) v).map .fail
  | .ctor 2 [v] => (Canonical.ofVal (α := CauseTerm) v).map .failCause
  | .ctor 3 [v] => (Canonical.ofVal (α := Term) v).map .yieldError
  | .ctor 4 [v] => (Canonical.ofVal (α := Term) v).map .sync
  | .ctor 5 [b] => (rawEff b).map .suspend
  | .ctor 6 [o, r] =>
    match Canonical.ofVal (α := NativeOp) o, Canonical.ofVal (α := Term) r with
    | some o, some r => some (.perform o r)
    | _, _ => none
  | .ctor 7 [a, b] =>
    match rawEff a, rawEff b with
    | some a, some b => some (.bind a b)
    | _, _ => none
  | .ctor 8 [s] => (rawStmts s).map .gen
  | .ctor 9 [b, h] =>
    match rawEff b, rawEff h with
    | some b, some h => some (.catchCause b h)
    | _, _ => none
  | .ctor 10 [b, v, c] =>
    match rawEff b, rawEff v, rawEff c with
    | some b, some v, some c => some (.matchCause b v c)
    | _, _, _ => none
  | .ctor 11 [b, f] =>
    match rawEff b, rawEff f with
    | some b, some f => some (.onExit b f)
    | _, _ => none
  | .ctor 12 [b] => (rawEff b).map .exit
  | .ctor 13 [b] => (rawEff b).map .uninterruptible
  | .ctor 14 [b] => (rawEff b).map .interruptible
  | .ctor 15 [t, a, b] =>
    match Canonical.ofVal (α := Term) t, rawEff a, rawEff b with
    | some t, some a, some b => some (.branch t a b)
    | _, _, _ => none
  | .ctor 16 [i, t, s, b] =>
    match Canonical.ofVal (α := Term) i, Canonical.ofVal (α := Term) t,
        Canonical.ofVal (α := Term) s, rawEff b with
    | some i, some t, some s, some b => some (.whileLoop i t s b)
    | _, _, _, _ => none
  | .ctor 17 [p] => (Canonical.ofVal (α := Nat) p).map .yieldNow
  | .ctor 18 [o, r] =>
    match Canonical.ofVal (α := NativeOp) o, Canonical.ofVal (α := Term) r with
    | some o, some r => some (.callback o r)
    | _, _ => none
  | .ctor 19 [f, m] =>
    match Canonical.ofVal (α := Term) f, Canonical.ofVal (α := ObserverMode) m with
    | some f, some m => some (.awaitFiber f m)
    | _, _ => none
  | .ctor 20 [a] => (rawAction a).map .withFiber
  | .ctor 21 [b] => (rawEff b).map .scoped
  | .ctor 22 [a, r] =>
    match rawEff a, rawEff r with
    | some a, some r => some (.acquireRelease a r)
    | _, _ => none
  | .ctor 23 [s, l, r] =>
    match Canonical.ofVal (α := Nat) s, rawEff l, rawEff r with
    | some s, some l, some r => some (.choose s l r)
    | _, _, _ => none
  | _ => none
def rawStmt : Val → Option (Stmt NativeOp)
  | .ctor 0 [e] => (rawEff e).map .bindYield
  | .ctor 1 [e] => (rawEff e).map .yieldDiscard
  | .ctor 2 [v] => (Canonical.ofVal (α := Term) v).map .ret
  | .ctor 3 [t, a, b] =>
    match Canonical.ofVal (α := Term) t, rawStmts a, rawStmts b with
    | some t, some a, some b => some (.ifElse t a b)
    | _, _, _ => none
  | .ctor 4 [b] => (rawStmts b).map .whileTrue
  | .ctor 5 [] => some .breakLoop
  | _ => none
def rawStmts : Val → Option (Stmts NativeOp)
  | .ctor 0 [] => some .nil
  | .ctor 1 [h, t] =>
    match rawStmt h, rawStmts t with
    | some h, some t => some (.cons h t)
    | _, _ => none
  | _ => none
def rawEffs : Val → Option (Effs NativeOp)
  | .ctor 0 [] => some .nil
  | .ctor 1 [h, t] =>
    match rawEff h, rawEffs t with
    | some h, some t => some (.cons h t)
    | _, _ => none
  | _ => none
def rawAction : Val → Option (ActionTerm NativeOp)
  | .ctor 0 [p, o] =>
    match rawEff p, Canonical.ofVal (α := ForkOptions) o with
    | some p, some o => some (.fork p o)
    | _, _ => none
  | .ctor 1 [p, o, s] =>
    match rawEff p, Canonical.ofVal (α := ForkOptions) o, Canonical.ofVal (α := Term) s with
    | some p, some o, some s => some (.forkIn p o s)
    | _, _, _ => none
  | .ctor 2 [p, o] =>
    match rawEff p, Canonical.ofVal (α := ForkOptions) o with
    | some p, some o => some (.forkScoped p o)
    | _, _ => none
  | .ctor 3 [t, s] =>
    match Canonical.ofVal (α := Term) t, Canonical.ofVal (α := Term) s with
    | some t, some s => some (.runIn t s)
    | _, _ => none
  | .ctor 4 [t] => (Canonical.ofVal (α := Term) t).map .interrupt
  | .ctor 5 [t] => (Canonical.ofVal (α := Term) t).map .interruptScoped
  | .ctor 6 [t, i] =>
    match Canonical.ofVal (α := Term) t, Canonical.ofVal (α := Option Term) i with
    | some t, some i => some (.interruptAll t i)
    | _, _ => none
  | .ctor 7 [t] => (Canonical.ofVal (α := Term) t).map .awaitAll
  | .ctor 8 [t] => (Canonical.ofVal (α := Term) t).map .awaitAllFailFast
  | .ctor 9 [] => some .snapshotChildren
  | .ctor 10 [s] => (Canonical.ofVal (α := Term) s).map .awaitNewChildren
  | .ctor 11 [es] => (rawEffs es).map .raceAll
  | .ctor 12 [c] => (Canonical.ofVal (α := Term) c).map .setContext
  | .ctor 13 [] => some .getContext
  | .ctor 14 [] => some .getId
  | .ctor 15 [s, e] =>
    match Canonical.ofVal (α := Term) s, Canonical.ofVal (α := Term) e with
    | some s, some e => some (.closeScope s e)
    | _, _ => none
  | _ => none
end

mutual
theorem rawEff_toValEff (p : Eff NativeOp) : rawEff (toValEff p) = some p := by
  cases p with
  | succeed v => simp [toValEff, rawEff, Canonical.ofVal_toVal]
  | fail e => simp [toValEff, rawEff, Canonical.ofVal_toVal]
  | failCause c => simp [toValEff, rawEff, Canonical.ofVal_toVal]
  | yieldError e => simp [toValEff, rawEff, Canonical.ofVal_toVal]
  | sync t => simp [toValEff, rawEff, Canonical.ofVal_toVal]
  | suspend b => simp [toValEff, rawEff, rawEff_toValEff b]
  | perform op r => simp [toValEff, rawEff, Canonical.ofVal_toVal]
  | bind a b => simp [toValEff, rawEff, rawEff_toValEff a, rawEff_toValEff b]
  | gen body => simp [toValEff, rawEff, rawStmts_toValStmts body]
  | catchCause b h => simp [toValEff, rawEff, rawEff_toValEff b, rawEff_toValEff h]
  | matchCause b v c =>
    simp [toValEff, rawEff, rawEff_toValEff b, rawEff_toValEff v, rawEff_toValEff c]
  | onExit b f => simp [toValEff, rawEff, rawEff_toValEff b, rawEff_toValEff f]
  | exit b => simp [toValEff, rawEff, rawEff_toValEff b]
  | uninterruptible b => simp [toValEff, rawEff, rawEff_toValEff b]
  | interruptible b => simp [toValEff, rawEff, rawEff_toValEff b]
  | branch t a b => simp [toValEff, rawEff, Canonical.ofVal_toVal, rawEff_toValEff a, rawEff_toValEff b]
  | whileLoop i t s b => simp [toValEff, rawEff, Canonical.ofVal_toVal, rawEff_toValEff b]
  | yieldNow p => simp [toValEff, rawEff, Canonical.ofVal_toVal]
  | callback reg r => simp [toValEff, rawEff, Canonical.ofVal_toVal]
  | awaitFiber f m => simp [toValEff, rawEff, Canonical.ofVal_toVal]
  | withFiber a => simp [toValEff, rawEff, rawAction_toValAction a]
  | «scoped» b => simp [toValEff, rawEff, rawEff_toValEff b]
  | acquireRelease a r => simp [toValEff, rawEff, rawEff_toValEff a, rawEff_toValEff r]
  | choose site l r => simp [toValEff, rawEff, Canonical.ofVal_toVal, rawEff_toValEff l, rawEff_toValEff r]
termination_by structural p
theorem rawStmt_toValStmt (s : Stmt NativeOp) : rawStmt (toValStmt s) = some s := by
  cases s with
  | bindYield e => simp [toValStmt, rawStmt, rawEff_toValEff e]
  | yieldDiscard e => simp [toValStmt, rawStmt, rawEff_toValEff e]
  | ret v => simp [toValStmt, rawStmt, Canonical.ofVal_toVal]
  | ifElse t a b => simp [toValStmt, rawStmt, Canonical.ofVal_toVal, rawStmts_toValStmts a, rawStmts_toValStmts b]
  | whileTrue b => simp [toValStmt, rawStmt, rawStmts_toValStmts b]
  | breakLoop => rfl
termination_by structural s
theorem rawStmts_toValStmts (s : Stmts NativeOp) : rawStmts (toValStmts s) = some s := by
  cases s with
  | nil => rfl
  | cons h t => simp [toValStmts, rawStmts, rawStmt_toValStmt h, rawStmts_toValStmts t]
termination_by structural s
theorem rawEffs_toValEffs (es : Effs NativeOp) : rawEffs (toValEffs es) = some es := by
  cases es with
  | nil => rfl
  | cons h t => simp [toValEffs, rawEffs, rawEff_toValEff h, rawEffs_toValEffs t]
termination_by structural es
theorem rawAction_toValAction (a : ActionTerm NativeOp) : rawAction (toValAction a) = some a := by
  cases a with
  | fork p o => simp [toValAction, rawAction, Canonical.ofVal_toVal, rawEff_toValEff p]
  | forkIn p o s => simp [toValAction, rawAction, Canonical.ofVal_toVal, rawEff_toValEff p]
  | forkScoped p o => simp [toValAction, rawAction, Canonical.ofVal_toVal, rawEff_toValEff p]
  | runIn t s => simp [toValAction, rawAction, Canonical.ofVal_toVal]
  | interrupt t => simp [toValAction, rawAction, Canonical.ofVal_toVal]
  | interruptScoped t => simp [toValAction, rawAction, Canonical.ofVal_toVal]
  | interruptAll t i => simp [toValAction, rawAction, Canonical.ofVal_toVal]
  | awaitAll t => simp [toValAction, rawAction, Canonical.ofVal_toVal]
  | awaitAllFailFast t => simp [toValAction, rawAction, Canonical.ofVal_toVal]
  | snapshotChildren => rfl
  | awaitNewChildren s => simp [toValAction, rawAction, Canonical.ofVal_toVal]
  | raceAll es => simp [toValAction, rawAction, rawEffs_toValEffs es]
  | setContext c => simp [toValAction, rawAction, Canonical.ofVal_toVal]
  | getContext => rfl
  | getId => rfl
  | closeScope s e => simp [toValAction, rawAction, Canonical.ofVal_toVal]
termination_by structural a
end

/-! The table memberships and the field lifts, one per field type. -/

theorem mem_eff : ("Eff", effShape) ∈ defs := List.Mem.head _
theorem mem_stmt : ("Stmt", stmtShape) ∈ defs := List.Mem.tail _ (List.Mem.head _)
theorem mem_stmts : ("Stmts", stmtsShape) ∈ defs :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
theorem mem_effs : ("Effs", effsShape) ∈ defs :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
theorem mem_action : ("ActionTerm", actionShape) ∈ defs :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

/-- Into the appended tail of the block's table. -/
theorem mem_tail {p : String × Shape}
    (h : p ∈ (shape Term).defs ++ (shape CauseTerm).defs ++ (shape NativeOp).defs ++
      (shape Nat).defs ++ (shape ObserverMode).defs ++ (shape ForkOptions).defs ++
      (shape (Option Term)).defs) : p ∈ defs :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ h))))

theorem lift_term (t : Term) : acceptsIn defs T (Canonical.toVal t) = true :=
  acceptsIn_mono_of_subset
    (fun _ hp => mem_tail (mem_append_of_left (mem_append_of_left (mem_append_of_left
      (mem_append_of_left (mem_append_of_left (mem_append_of_left hp)))))))
    _ _ (Canonical.fits t)

theorem lift_cause (c : CauseTerm) : acceptsIn defs (shape CauseTerm).root (Canonical.toVal c) = true :=
  acceptsIn_mono_of_subset
    (fun _ hp => mem_tail (mem_append_of_left (mem_append_of_left (mem_append_of_left
      (mem_append_of_left (mem_append_of_left (mem_append_of_right hp)))))))
    _ _ (Canonical.fits c)

theorem lift_op (o : NativeOp) : acceptsIn defs (shape NativeOp).root (Canonical.toVal o) = true :=
  acceptsIn_mono_of_subset
    (fun _ hp => mem_tail (mem_append_of_left (mem_append_of_left (mem_append_of_left
      (mem_append_of_left (mem_append_of_right hp))))))
    _ _ (Canonical.fits o)

theorem lift_nat (n : Nat) : acceptsIn defs (shape Nat).root (Canonical.toVal n) = true :=
  acceptsIn_mono_of_subset
    (fun _ hp => mem_tail (mem_append_of_left (mem_append_of_left (mem_append_of_left
      (mem_append_of_right hp)))))
    _ _ (Canonical.fits n)

theorem lift_mode (m : ObserverMode) :
    acceptsIn defs (shape ObserverMode).root (Canonical.toVal m) = true :=
  acceptsIn_mono_of_subset
    (fun _ hp => mem_tail (mem_append_of_left (mem_append_of_left (mem_append_of_right hp))))
    _ _ (Canonical.fits m)

theorem lift_fork (o : ForkOptions) :
    acceptsIn defs (shape ForkOptions).root (Canonical.toVal o) = true :=
  acceptsIn_mono_of_subset
    (fun _ hp => mem_tail (mem_append_of_left (mem_append_of_right hp)))
    _ _ (Canonical.fits o)

theorem lift_opt (o : Option Term) :
    acceptsIn defs (shape (Option Term)).root (Canonical.toVal o) = true :=
  acceptsIn_mono_of_subset (fun _ hp => mem_tail (mem_append_of_right hp)) _ _ (Canonical.fits o)

mutual
theorem fitsEff (p : Eff NativeOp) : acceptsIn defs E (toValEff p) = true := by
  apply accepts_named_of_mem _ _ effShape _ mem_eff
  cases p with
  | succeed v =>
    exact acceptsAt_sum _ _ _ 0 "succeed" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (lift_term v) (acceptsFields_nil _))
  | fail e =>
    exact acceptsAt_sum _ _ _ 1 "fail" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (lift_term e) (acceptsFields_nil _))
  | failCause c =>
    exact acceptsAt_sum _ _ _ 2 "failCause" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (lift_cause c) (acceptsFields_nil _))
  | yieldError e =>
    exact acceptsAt_sum _ _ _ 3 "yieldError" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (lift_term e) (acceptsFields_nil _))
  | sync t =>
    exact acceptsAt_sum _ _ _ 4 "sync" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (lift_term t) (acceptsFields_nil _))
  | suspend b =>
    exact acceptsAt_sum _ _ _ 5 "suspend" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (fitsEff b) (acceptsFields_nil _))
  | perform op r =>
    exact acceptsAt_sum _ _ _ 6 "perform" _ _ rfl (acceptsFields_cons _ _ _ _ _ _ (lift_op op)
      (acceptsFields_cons _ _ _ _ _ _ (lift_term r) (acceptsFields_nil _)))
  | bind a b =>
    exact acceptsAt_sum _ _ _ 7 "bind" _ _ rfl (acceptsFields_cons _ _ _ _ _ _ (fitsEff a)
      (acceptsFields_cons _ _ _ _ _ _ (fitsEff b) (acceptsFields_nil _)))
  | gen body =>
    exact acceptsAt_sum _ _ _ 8 "gen" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (fitsStmts body) (acceptsFields_nil _))
  | catchCause b h =>
    exact acceptsAt_sum _ _ _ 9 "catchCause" _ _ rfl (acceptsFields_cons _ _ _ _ _ _ (fitsEff b)
      (acceptsFields_cons _ _ _ _ _ _ (fitsEff h) (acceptsFields_nil _)))
  | matchCause b v c =>
    exact acceptsAt_sum _ _ _ 10 "matchCause" _ _ rfl (acceptsFields_cons _ _ _ _ _ _ (fitsEff b)
      (acceptsFields_cons _ _ _ _ _ _ (fitsEff v)
        (acceptsFields_cons _ _ _ _ _ _ (fitsEff c) (acceptsFields_nil _))))
  | onExit b f =>
    exact acceptsAt_sum _ _ _ 11 "onExit" _ _ rfl (acceptsFields_cons _ _ _ _ _ _ (fitsEff b)
      (acceptsFields_cons _ _ _ _ _ _ (fitsEff f) (acceptsFields_nil _)))
  | exit b =>
    exact acceptsAt_sum _ _ _ 12 "exit" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (fitsEff b) (acceptsFields_nil _))
  | uninterruptible b =>
    exact acceptsAt_sum _ _ _ 13 "uninterruptible" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (fitsEff b) (acceptsFields_nil _))
  | interruptible b =>
    exact acceptsAt_sum _ _ _ 14 "interruptible" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (fitsEff b) (acceptsFields_nil _))
  | branch t a b =>
    exact acceptsAt_sum _ _ _ 15 "branch" _ _ rfl (acceptsFields_cons _ _ _ _ _ _ (lift_term t)
      (acceptsFields_cons _ _ _ _ _ _ (fitsEff a)
        (acceptsFields_cons _ _ _ _ _ _ (fitsEff b) (acceptsFields_nil _))))
  | whileLoop i t s b =>
    exact acceptsAt_sum _ _ _ 16 "whileLoop" _ _ rfl (acceptsFields_cons _ _ _ _ _ _ (lift_term i)
      (acceptsFields_cons _ _ _ _ _ _ (lift_term t)
        (acceptsFields_cons _ _ _ _ _ _ (lift_term s)
          (acceptsFields_cons _ _ _ _ _ _ (fitsEff b) (acceptsFields_nil _)))))
  | yieldNow p =>
    exact acceptsAt_sum _ _ _ 17 "yieldNow" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (lift_nat p) (acceptsFields_nil _))
  | callback reg r =>
    exact acceptsAt_sum _ _ _ 18 "callback" _ _ rfl (acceptsFields_cons _ _ _ _ _ _ (lift_op reg)
      (acceptsFields_cons _ _ _ _ _ _ (lift_term r) (acceptsFields_nil _)))
  | awaitFiber f m =>
    exact acceptsAt_sum _ _ _ 19 "awaitFiber" _ _ rfl (acceptsFields_cons _ _ _ _ _ _ (lift_term f)
      (acceptsFields_cons _ _ _ _ _ _ (lift_mode m) (acceptsFields_nil _)))
  | withFiber a =>
    exact acceptsAt_sum _ _ _ 20 "withFiber" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (fitsAction a) (acceptsFields_nil _))
  | «scoped» b =>
    exact acceptsAt_sum _ _ _ 21 "scoped" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (fitsEff b) (acceptsFields_nil _))
  | acquireRelease a r =>
    exact acceptsAt_sum _ _ _ 22 "acquireRelease" _ _ rfl (acceptsFields_cons _ _ _ _ _ _ (fitsEff a)
      (acceptsFields_cons _ _ _ _ _ _ (fitsEff r) (acceptsFields_nil _)))
  | choose site l r =>
    exact acceptsAt_sum _ _ _ 23 "choose" _ _ rfl (acceptsFields_cons _ _ _ _ _ _ (lift_nat site)
      (acceptsFields_cons _ _ _ _ _ _ (fitsEff l)
        (acceptsFields_cons _ _ _ _ _ _ (fitsEff r) (acceptsFields_nil _))))
termination_by structural p
theorem fitsStmt (s : Stmt NativeOp) : acceptsIn defs (.named "Stmt") (toValStmt s) = true := by
  apply accepts_named_of_mem _ _ stmtShape _ mem_stmt
  cases s with
  | bindYield e =>
    exact acceptsAt_sum _ _ _ 0 "bindYield" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (fitsEff e) (acceptsFields_nil _))
  | yieldDiscard e =>
    exact acceptsAt_sum _ _ _ 1 "yieldDiscard" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (fitsEff e) (acceptsFields_nil _))
  | ret v =>
    exact acceptsAt_sum _ _ _ 2 "ret" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (lift_term v) (acceptsFields_nil _))
  | ifElse t a b =>
    exact acceptsAt_sum _ _ _ 3 "ifElse" _ _ rfl (acceptsFields_cons _ _ _ _ _ _ (lift_term t)
      (acceptsFields_cons _ _ _ _ _ _ (fitsStmts a)
        (acceptsFields_cons _ _ _ _ _ _ (fitsStmts b) (acceptsFields_nil _))))
  | whileTrue b =>
    exact acceptsAt_sum _ _ _ 4 "whileTrue" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (fitsStmts b) (acceptsFields_nil _))
  | breakLoop => exact acceptsAt_sum _ _ _ 5 "breakLoop" [] [] rfl (acceptsFields_nil _)
termination_by structural s
theorem fitsStmts (s : Stmts NativeOp) : acceptsIn defs (.named "Stmts") (toValStmts s) = true := by
  apply accepts_named_of_mem _ _ stmtsShape _ mem_stmts
  cases s with
  | nil => exact acceptsAt_sum _ _ _ 0 "nil" [] [] rfl (acceptsFields_nil _)
  | cons h t =>
    exact acceptsAt_sum _ _ _ 1 "cons" _ _ rfl (acceptsFields_cons _ _ _ _ _ _ (fitsStmt h)
      (acceptsFields_cons _ _ _ _ _ _ (fitsStmts t) (acceptsFields_nil _)))
termination_by structural s
theorem fitsEffs (es : Effs NativeOp) : acceptsIn defs (.named "Effs") (toValEffs es) = true := by
  apply accepts_named_of_mem _ _ effsShape _ mem_effs
  cases es with
  | nil => exact acceptsAt_sum _ _ _ 0 "nil" [] [] rfl (acceptsFields_nil _)
  | cons h t =>
    exact acceptsAt_sum _ _ _ 1 "cons" _ _ rfl (acceptsFields_cons _ _ _ _ _ _ (fitsEff h)
      (acceptsFields_cons _ _ _ _ _ _ (fitsEffs t) (acceptsFields_nil _)))
termination_by structural es
theorem fitsAction (a : ActionTerm NativeOp) :
    acceptsIn defs (.named "ActionTerm") (toValAction a) = true := by
  apply accepts_named_of_mem _ _ actionShape _ mem_action
  cases a with
  | fork p o =>
    exact acceptsAt_sum _ _ _ 0 "fork" _ _ rfl (acceptsFields_cons _ _ _ _ _ _ (fitsEff p)
      (acceptsFields_cons _ _ _ _ _ _ (lift_fork o) (acceptsFields_nil _)))
  | forkIn p o s =>
    exact acceptsAt_sum _ _ _ 1 "forkIn" _ _ rfl (acceptsFields_cons _ _ _ _ _ _ (fitsEff p)
      (acceptsFields_cons _ _ _ _ _ _ (lift_fork o)
        (acceptsFields_cons _ _ _ _ _ _ (lift_term s) (acceptsFields_nil _))))
  | forkScoped p o =>
    exact acceptsAt_sum _ _ _ 2 "forkScoped" _ _ rfl (acceptsFields_cons _ _ _ _ _ _ (fitsEff p)
      (acceptsFields_cons _ _ _ _ _ _ (lift_fork o) (acceptsFields_nil _)))
  | runIn t s =>
    exact acceptsAt_sum _ _ _ 3 "runIn" _ _ rfl (acceptsFields_cons _ _ _ _ _ _ (lift_term t)
      (acceptsFields_cons _ _ _ _ _ _ (lift_term s) (acceptsFields_nil _)))
  | interrupt t =>
    exact acceptsAt_sum _ _ _ 4 "interrupt" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (lift_term t) (acceptsFields_nil _))
  | interruptScoped t =>
    exact acceptsAt_sum _ _ _ 5 "interruptScoped" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (lift_term t) (acceptsFields_nil _))
  | interruptAll t i =>
    exact acceptsAt_sum _ _ _ 6 "interruptAll" _ _ rfl (acceptsFields_cons _ _ _ _ _ _ (lift_term t)
      (acceptsFields_cons _ _ _ _ _ _ (lift_opt i) (acceptsFields_nil _)))
  | awaitAll t =>
    exact acceptsAt_sum _ _ _ 7 "awaitAll" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (lift_term t) (acceptsFields_nil _))
  | awaitAllFailFast t =>
    exact acceptsAt_sum _ _ _ 8 "awaitAllFailFast" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (lift_term t) (acceptsFields_nil _))
  | snapshotChildren => exact acceptsAt_sum _ _ _ 9 "snapshotChildren" [] [] rfl (acceptsFields_nil _)
  | awaitNewChildren s =>
    exact acceptsAt_sum _ _ _ 10 "awaitNewChildren" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (lift_term s) (acceptsFields_nil _))
  | raceAll es =>
    exact acceptsAt_sum _ _ _ 11 "raceAll" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (fitsEffs es) (acceptsFields_nil _))
  | setContext c =>
    exact acceptsAt_sum _ _ _ 12 "setContext" _ _ rfl
      (acceptsFields_cons _ _ _ _ _ _ (lift_term c) (acceptsFields_nil _))
  | getContext => exact acceptsAt_sum _ _ _ 13 "getContext" [] [] rfl (acceptsFields_nil _)
  | getId => exact acceptsAt_sum _ _ _ 14 "getId" [] [] rfl (acceptsFields_nil _)
  | closeScope s e =>
    exact acceptsAt_sum _ _ _ 15 "closeScope" _ _ rfl (acceptsFields_cons _ _ _ _ _ _ (lift_term s)
      (acceptsFields_cons _ _ _ _ _ _ (lift_term e) (acceptsFields_nil _)))
termination_by structural a
end

instance instCanonicalEff : Canonical (Eff NativeOp) :=
  ⟨⟨E, defs⟩, toValEff, guarded toValEff rawEff,
    fun p => guarded_toVal _ _ p (rawEff_toValEff p), fun h => guarded_exact h, fitsEff⟩

instance instCanonicalStmt : Canonical (Stmt NativeOp) :=
  ⟨⟨.named "Stmt", defs⟩, toValStmt, guarded toValStmt rawStmt,
    fun s => guarded_toVal _ _ s (rawStmt_toValStmt s), fun h => guarded_exact h, fitsStmt⟩

instance instCanonicalStmts : Canonical (Stmts NativeOp) :=
  ⟨⟨.named "Stmts", defs⟩, toValStmts, guarded toValStmts rawStmts,
    fun s => guarded_toVal _ _ s (rawStmts_toValStmts s), fun h => guarded_exact h, fitsStmts⟩

instance instCanonicalEffs : Canonical (Effs NativeOp) :=
  ⟨⟨.named "Effs", defs⟩, toValEffs, guarded toValEffs rawEffs,
    fun es => guarded_toVal _ _ es (rawEffs_toValEffs es), fun h => guarded_exact h, fitsEffs⟩

instance instCanonicalAction : Canonical (ActionTerm NativeOp) :=
  ⟨⟨.named "ActionTerm", defs⟩, toValAction, guarded toValAction rawAction,
    fun a => guarded_toVal _ _ a (rawAction_toValAction a), fun h => guarded_exact h, fitsAction⟩

end EffC

/-! ## The corpus (`Wire.lean:576-618`), byte-identical to the goldens under `ocaml/goldens/eff` -/

namespace Corpus

def forkOptions : ForkOptions := { startImmediately := false, daemon := false, maskMode := .inherit }

def p42 : Eff NativeOp := .succeed (.lit (.nat 42))
def pBind : Eff NativeOp :=
  .bind (.succeed (.lit (.nat 1))) (.succeed (.app "succ" (.cons (.var 0) .nil)))
def pFork : Eff NativeOp :=
  .bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat 7)))) forkOptions))
    (.awaitFiber (.var 0) .awaitValue)
def pAwait : Eff NativeOp :=
  .bind (.perform .deferredMake (.lit .unit)) (.perform .deferredAwait (.var 0))
def pGen : Eff NativeOp :=
  .gen (.cons (.bindYield (.succeed (.lit (.nat 3))))
    (.cons (.ifElse (.app "isZero" (.cons (.var 0) .nil)) (.cons (.ret (.lit (.bool true))) .nil)
      (.cons (.ret (.lit (.bool false))) .nil)) .nil))
def pLoop : Eff NativeOp :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.whileLoop (.lit (.nat 0)) (.app "isZero" (.cons (.var 1) .nil))
      (.app "succ" (.cons (.var 1) .nil)) (.perform (.refUpdate .incr) (.var 0)))
def pCatch : Eff NativeOp :=
  .catchCause (.failCause (.both (.fail (.lit (.nat 1))) (.interrupt none)))
    (.succeed (.lit .unit))
def pScope : Eff NativeOp :=
  .scoped (.bind (.perform (.scopeMake .parallel) (.lit .unit))
    (.bind (.exit (.succeed (.lit (.nat 1))))
      (.withFiber (.closeScope (.var 0) (.var 1)))))

def all : List (Eff NativeOp) := [p42, pBind, pFork, pAwait, pGen, pLoop, pCatch, pScope]

/-- The canonical bytes as lowercase hex, the goldens' spelling. -/
def hexOf (p : Eff NativeOp) : String := hexString (Canonical.encode p)

end Corpus

open Corpus in
#guard hexOf p42 =
  "0a00000000000000390200000000000000000a0000000000000027020000000000000001010a0000000000000014020000000000000001010200000000000000012a"
open Corpus in
#guard hexOf pBind =
  "0a00000000000000be020000000000000001070a00000000000000390200000000000000000a0000000000000027020000000000000001010a000000000000001402000000000000000101020000000000000001010a00000000000000690200000000000000000a000000000000005702000000000000000102030000000000000004737563630a0000000000000037020000000000000001010a00000000000000120200000000000000000200000000000000000a0000000000000009020000000000000000"
open Corpus in
#guard hexOf pFork =
  "0a0000000000000119020000000000000001070a00000000000000c6020000000000000001140a00000000000000b30200000000000000000a0000000000000068020000000000000001070a0000000000000013020000000000000001110200000000000000000a00000000000000390200000000000000000a0000000000000027020000000000000001010a000000000000001402000000000000000101020000000000000001070a000000000000003002000000000000000001000000000000000100010000000000000001000a000000000000000a020000000000000001020a0000000000000037020000000000000001130a00000000000000120200000000000000000200000000000000000a0000000000000009020000000000000000"
open Corpus in
#guard hexOf pAwait =
  "0a0000000000000096020000000000000001070a0000000000000042020000000000000001060a000000000000000a0200000000000000010d0a000000000000001c020000000000000001010a00000000000000090200000000000000000a0000000000000038020000000000000001060a000000000000000a020000000000000001120a0000000000000012020000000000000000020000000000000000"
open Corpus in
#guard hexOf pGen =
  "0a00000000000001db020000000000000001080a00000000000001c8020000000000000001010a000000000000004b0200000000000000000a00000000000000390200000000000000000a0000000000000027020000000000000001010a000000000000001402000000000000000101020000000000000001030a0000000000000161020000000000000001010a000000000000013c020000000000000001030a00000000000000590200000000000000010203000000000000000669735a65726f0a0000000000000037020000000000000001010a00000000000000120200000000000000000200000000000000000a00000000000000090200000000000000000a000000000000005f020000000000000001010a000000000000003a020000000000000001020a0000000000000027020000000000000001010a000000000000001402000000000000000102010000000000000001010a00000000000000090200000000000000000a000000000000005f020000000000000001010a000000000000003a020000000000000001020a0000000000000027020000000000000001010a000000000000001402000000000000000102010000000000000001000a00000000000000090200000000000000000a0000000000000009020000000000000000"
open Corpus in
#guard hexOf pLoop =
  "0a00000000000001b7020000000000000001070a000000000000004b020000000000000001060a00000000000000090200000000000000000a0000000000000026020000000000000001010a0000000000000013020000000000000001010200000000000000000a0000000000000150020000000000000001100a0000000000000026020000000000000001010a0000000000000013020000000000000001010200000000000000000a000000000000005a0200000000000000010203000000000000000669735a65726f0a0000000000000038020000000000000001010a0000000000000013020000000000000000020000000000000001010a00000000000000090200000000000000000a000000000000005802000000000000000102030000000000000004737563630a0000000000000038020000000000000001010a0000000000000013020000000000000000020000000000000001010a00000000000000090200000000000000000a000000000000004a020000000000000001060a000000000000001c020000000000000001050a00000000000000090200000000000000000a0000000000000012020000000000000000020000000000000000"
open Corpus in
#guard hexOf pCatch =
  "0a00000000000000c5020000000000000001090a000000000000007b020000000000000001020a0000000000000068020000000000000001030a00000000000000390200000000000000000a0000000000000027020000000000000001010a000000000000001402000000000000000101020000000000000001010a0000000000000013020000000000000001020600000000000000000a000000000000002e0200000000000000000a000000000000001c020000000000000001010a0000000000000009020000000000000000"
open Corpus in
#guard hexOf pScope =
  "0a0000000000000140020000000000000001150a000000000000012d020000000000000001070a0000000000000055020000000000000001060a000000000000001d020000000000000001130a000000000000000a020000000000000001010a000000000000001c020000000000000001010a00000000000000090200000000000000000a00000000000000bc020000000000000001070a000000000000004c0200000000000000010c0a00000000000000390200000000000000000a0000000000000027020000000000000001010a000000000000001402000000000000000101020000000000000001010a0000000000000054020000000000000001140a00000000000000410200000000000000010f0a00000000000000120200000000000000000200000000000000000a000000000000001302000000000000000002000000000000000101"
open Corpus in
#guard (Canonical.encode p42).length = 66
open Corpus in
#guard (Canonical.digest p42).hex = "fa5f40f054198e91b2446522308e197b0a02c4edfe823f894763d3aa63ad62a3"
open Corpus in
#guard all.all fun p => Canonical.decode (Canonical.encode p) = some p
open Corpus in
#guard all.all fun p => Canonical.decode (α := Eff NativeOp) (Canonical.encode p ++ [0]) = none
open Corpus in
#guard all.all fun p => Canonical.decode (α := Eff NativeOp) (Canonical.encode p).dropLast = none
-- A non-canonical natural (leading zero digit) inside a program is refused (`Wire.lean:628`).
#guard Canonical.decode (α := Eff NativeOp)
  (framed Tag.ctor (framed Tag.nat [0, 17] ++ Canonical.encode (Term.lit .unit))) = none
open Corpus in
#guard all.all fun p => (shape (Eff NativeOp)).accepts (Canonical.toVal p)

end ProgramCanonical

/-! ## Receipts -/

#print axioms ProgramCanonical.LitC.instCanonical
#print axioms ProgramCanonical.FnNameC.instCanonical
#print axioms ProgramCanonical.StrategyC.instCanonical
#print axioms ProgramCanonical.MaskModeC.instCanonical
#print axioms ProgramCanonical.ObserverModeC.instCanonical
#print axioms ProgramCanonical.NativeOpC.ofVal_exact
#print axioms ProgramCanonical.NativeOpC.fits
#print axioms ProgramCanonical.NativeOpC.instCanonical
#print axioms ProgramCanonical.ForkOptionsC.instCanonical
#print axioms ProgramCanonical.TermC.rawT_toValT
#print axioms ProgramCanonical.TermC.fitsT
#print axioms ProgramCanonical.TermC.instCanonicalTerm
#print axioms ProgramCanonical.TermC.instCanonicalTerms
#print axioms ProgramCanonical.CauseC.instCanonical
#print axioms ProgramCanonical.EffC.toValEff
#print axioms ProgramCanonical.EffC.rawEff
#print axioms ProgramCanonical.EffC.rawEff_toValEff
#print axioms ProgramCanonical.EffC.fitsEff
#print axioms ProgramCanonical.EffC.instCanonicalEff
#print axioms ProgramCanonical.EffC.instCanonicalStmt
#print axioms ProgramCanonical.EffC.instCanonicalStmts
#print axioms ProgramCanonical.EffC.instCanonicalEffs
#print axioms ProgramCanonical.EffC.instCanonicalAction

end Effect4.Store
