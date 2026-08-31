import Cas.Lang.Representation
import Cas.Backend.Universal

/-!
# Judge E — adversarial check of position E ("layer-as-content-plus-interpreter")

Position E's carrier, reproduced VERBATIM from
`workshop/layer/propose-E.lean`, then attacked.

Three findings, all kernel-checked:

* §A  `through_monoid` is NOT recovered. `Layer := Handler SvcSig (Prog LayerSig)`
      is not `Handler S (Prog S)`. The claim is the design's self-declared
      "biggest single saving"; the file never cites it and cannot.
* §B  THE KILLER. Position E has NO BUILD STEP. An `.acquires` leaf is
      re-entered per ASK, so the resource is acquired and released once per
      USE. The claim "lifetime here is the description's tree shape" is false.
* §C  `merge_needs_the_content` is a tautology about an explicit argument.
      The statement E needed is TRUE and provable — E did not prove it.
      (Salvage: §C2 supplies the real theorem.)
-/

namespace JudgeE
open Cas Cas.Lang

/-! ## 0. Position E's carrier, verbatim -/

abbrev SvcKey := String
abbrev BlockId := Nat

inductive SvcE where
  | ask (key : SvcKey)
  deriving DecidableEq, Repr
abbrev SvcE.Ans : SvcE → Type | .ask _ => Addr32
abbrev SvcSig : Sig := ⟨SvcE, SvcE.Ans⟩

inductive ScopeE where
  | ensuringExit (body onOk onErr : BlockId)
  | raise (err : Addr32)
  deriving DecidableEq, Repr
abbrev ScopeE.Ans : ScopeE → Type
  | .ensuringExit _ _ _ => Addr32
  | .raise _ => Empty
abbrev ScopeSig : Sig := ⟨ScopeE, ScopeE.Ans⟩

abbrev LayerSig : Sig := SvcSig ⊕ₛ ScopeSig
abbrev Layer := Handler SvcSig (Prog LayerSig)

def injSvc : Layer where handle op := Prog.op (S := LayerSig) (Sum.inl op)

def scopePass : Handler ScopeSig (Prog LayerSig) where
  handle op := Prog.op (S := LayerSig) (Sum.inr op)

def leafH (k : SvcKey) (body : Prog LayerSig Addr32) : Layer where
  handle
    | .ask k' => if k' = k then body else Prog.op (S := LayerSig) (Sum.inl (SvcE.ask k'))

def mergeOn {M : Type → Type v} (keys : List SvcKey)
    (l r : Handler SvcSig M) : Handler SvcSig M where
  handle
    | .ask k => if keys.contains k then l.handle (.ask k) else r.handle (.ask k)

def liftL (u : Layer) : Handler LayerSig (Prog LayerSig) := Handler.sum u scopePass

def Layer.provide (outer inner : Layer) : Layer := outer.through (liftL inner)

inductive LDesc where
  | empty
  | leaf     (key : SvcKey) (requires : List SvcKey) (body : BlockId)
  | acquires (key : SvcKey) (requires : List SvcKey)
             (acquire onOk onErr : BlockId)
  | merge    (l r : LDesc)
  | provide  (inner outer : LDesc)
  | fresh    (nonce : Nat) (inner : LDesc)
  deriving DecidableEq, Repr

def LDesc.provides : LDesc → List SvcKey
  | .empty => []
  | .leaf k _ _ => [k]
  | .acquires k _ _ _ _ => [k]
  | .merge l r => l.provides ++ r.provides
  | .provide _ o => o.provides
  | .fresh _ i => i.provides

abbrev CodeEnv := BlockId → Prog LayerSig Addr32

def LDesc.build (ce : CodeEnv) : LDesc → Layer
  | .empty => injSvc
  | .leaf k _ b => leafH k (ce b)
  | .acquires k _ acq onOk onErr =>
      leafH k (Prog.op (S := LayerSig) (Sum.inr (ScopeE.ensuringExit acq onOk onErr)))
  | .merge l r => mergeOn l.provides (l.build ce) (r.build ce)
  | .provide i o => Layer.provide (o.build ce) (i.build ce)
  | .fresh _ i => i.build ce

abbrev WM := ExceptT Refusal (StateM Word)
abbrev WComp := Word → Except Refusal Addr32 × Word

def ensuringExitT (body onOk onErr : WComp) : WComp := fun w =>
  match body w with
  | (.ok a, w₁) =>
    match onOk w₁ with
    | (.ok _, w₂) => (.ok a, w₂)
    | (.error r, w₂) => (.error r, w₂)
  | (.error r, w₁) => (.error r, (onErr w₁).2)

def scopeW (wce : BlockId → WComp) : Handler ScopeSig WM where
  handle
    | .ensuringExit b o e => ensuringExitT (wce b) (wce o) (wce e)
    | .raise _ => fun w => (.error (.failed "scope: raised"), w)

def bottom (svc : Handler SvcSig WM) (wce : BlockId → WComp) : Handler LayerSig WM :=
  Handler.sum svc (scopeW wce)

def a0 : Addr32 := ⟨List.replicate 32 0, by simp⟩
def a1 : Addr32 := ⟨List.replicate 32 1, by simp⟩

/-! ## §A. `through_monoid` is NOT recovered.

Position E, `whatItBuys` #2: "`through_monoid` IS RECOVERED. … Under R7
there IS one signature … So the theorem applies verbatim and
`provide_assoc` / both unit laws come free. That is the design's biggest
single saving and it costs nothing."

`through_monoid` (`Universal.lean:785`) is
  `{S : Sig} (t u v : Handler S (Prog S)) : …`
— ENDOMORPHISMS at ONE signature. Position E's `Layer` is
`Handler SvcSig (Prog LayerSig)` with `LayerSig := SvcSig ⊕ₛ ScopeSig`.
Applying `through_monoid` at `Layer` needs `SvcSig ≡ LayerSig`.

Uncommenting the next line is an elaboration error (recorded in the
report; left commented so this file compiles):

    example (t u v : Layer) := through_monoid t u v

The design is in exactly the cross-signature CATEGORY setting every rival
is in. `through_assoc` still applies — but only after a NEW lemma
(`liftL_through`) that the endomorphism reading would not need. The saving
claimed is not taken, and the file never cites `through_monoid`.

The two signatures differ at their operation type, which the kernel sees: -/

theorem svc_op_is_not_layer_op : (LayerSig.Op) = (SvcE ⊕ ScopeE) := rfl
theorem svc_op_is_svcE : (SvcSig.Op) = SvcE := rfl

/-! ## §B. THE KILLER — position E has no build step.

`whatItBuys` claims the design fixes LIFETIME: "what memoization actually
decides is LIFETIME, not cost — and lifetime here is the description's tree
shape, which `ensuringExitT` nesting already fixes."

It does not. `LDesc.build` maps `.acquires` to a leaf whose CLAUSE is the
`ensuringExit` operation. A handler clause is re-entered on every
dispatch, so one `.acquires` node in the description acquires and releases
once per ASK. -/

def nAcq : Node := ⟨0, 7, [], []⟩
def nRel : Node := ⟨0, 9, [], []⟩

def mark (n : Node) : WComp := fun w => (.ok a0, w ++ [Binding.mk a0 n])

/-- Block 0 = acquire (marks), block 1 = release (marks). -/
def wce0 : BlockId → WComp
  | 0 => mark nAcq
  | 1 => mark nRel
  | _ => fun w => (.ok a0, w)

def svc0 : Handler SvcSig WM := ⟨fun _ => fun w => (.ok a0, w)⟩
def ce0 : CodeEnv := fun _ => Prog.pure a0

/-- ONE acquiring layer in the description: a connection pool. -/
def dPool : LDesc := .acquires "Db" [] 0 1 1

/-- A consumer that uses the service TWICE. -/
def useTwice : Prog SvcSig Addr32 :=
  .vis (SvcE.ask "Db") (fun _ => .vis (SvcE.ask "Db") (fun a => .pure a))

def useOnce : Prog SvcSig Addr32 := .vis (SvcE.ask "Db") (fun a => .pure a)

def runE (p : Prog SvcSig Addr32) : WComp :=
  interpret (bottom svc0 wce0) (interpret (dPool.build ce0) p)

/-- **One use: acquire, release.** -/
theorem one_use_acquires_once :
    (runE useOnce []).2 = [Binding.mk a0 nAcq, Binding.mk a0 nRel] := rfl

/-- **THE FALSIFIER. Two uses of ONE `.acquires` node acquire TWICE.**
A layer exists to build a resource once and serve it many times. Position
E's builder cannot: the description's tree shape does not fix lifetime,
because the clause is re-entered per dispatch. This is
`through_pays_twice` (position C), `build_step_is_observable` (position A)
and `through_erases_the_build` (position D) landing on position E's own
carrier, through position E's own scope story. -/
theorem position_E_reacquires_per_use :
    (runE useTwice []).2
      = [Binding.mk a0 nAcq, Binding.mk a0 nRel,
         Binding.mk a0 nAcq, Binding.mk a0 nRel] := rfl

/-- …and the counts are genuinely different, so this is not a vacuity. -/
theorem build_step_is_missing :
    (runE useTwice []).2.length ≠ (runE useOnce []).2.length := by decide

/-- **The release is also wrong, not just repeated.** The resource is
released BEFORE the second use — so the second use runs against a
finalized resource. LIFO nesting cannot help: there is no nesting, there
are two sibling brackets. -/
theorem release_happens_before_the_second_use :
    (runE useTwice []).2.take 2 = [Binding.mk a0 nAcq, Binding.mk a0 nRel] := rfl

/-! ### `provide` does not repair it either. -/

/-- An outer layer that answers "App" by using "Db" twice. -/
def dApp : LDesc := .leaf "App" ["Db"] 5

def ceApp : CodeEnv
  | 5 => (Prog.op (S := LayerSig) (Sum.inl (SvcE.ask "Db"))).bind
           (fun _ => Prog.op (S := LayerSig) (Sum.inl (SvcE.ask "Db")))
  | _ => Prog.pure a0

/-- `provide` the pool into the app, then ask ONCE for "App". -/
def runProvided : WComp :=
  interpret (bottom svc0 wce0)
    (((LDesc.provide dPool dApp).build ceApp).handle (SvcE.ask "App"))

/-- **Providing an acquiring layer to a consumer that uses it twice
acquires twice.** This is the shape `Layer` exists for, and it is exactly
the shape that fails. -/
theorem provide_reacquires_per_use :
    (runProvided []).2
      = [Binding.mk a0 nAcq, Binding.mk a0 nRel,
         Binding.mk a0 nAcq, Binding.mk a0 nRel] := rfl

/-! ## §C. `merge_needs_the_content` proves nothing about content.

E's theorem is `mergeOn ["A"] lA rA ≠ mergeOn [] lA rA` — a function
given two different values of an EXPLICIT argument returns two different
results. It is a fact about `mergeOn`'s signature, not about layers. Any
non-constant function of any argument satisfies it: -/

def anyFn (b : Bool) (l r : Addr32) : Addr32 := if b then l else r

theorem the_same_shape_holds_for_a_bool :
    anyFn true a0 a1 ≠ anyFn false a0 a1 := by
  intro h
  have : (List.replicate 32 (0:UInt8)) = List.replicate 32 1 :=
    congrArg Subtype.val h
  simp at this

/-! ### §C2. SALVAGE — the statement E needed IS true, and here it is.

The real claim is: two descriptions whose BUILDS are equal have different
MERGES, so `merge` is not a function of the code half. E asserted this in
prose ("recovering a provides-set from a builder means deciding equality of
`Prog LayerSig Addr32`") and exhibited something else. It holds. -/

def ceF : CodeEnv
  | 0 => Prog.op (S := LayerSig) (Sum.inl (SvcE.ask "A"))
  | _ => Prog.pure a1

/-- Two DIFFERENT descriptions — one provides "A", one provides nothing. -/
def dProvidesA : LDesc := .leaf "A" [] 0
def dProvidesNothing : LDesc := .empty
def dOther : LDesc := .leaf "A" [] 1

/-- Their builders are EQUAL: a leaf whose body forwards its own ask IS
the forwarding handler. -/
theorem builds_agree : dProvidesA.build ceF = dProvidesNothing.build ceF :=
  Handler.ext fun op => by
    cases op with
    | ask k =>
      by_cases h : k = "A"
      · subst h; rfl
      · show (if k = "A" then ceF 0 else Prog.op (S := LayerSig) (Sum.inl (SvcE.ask k)))
            = Prog.op (S := LayerSig) (Sum.inl (SvcE.ask k))
        exact if_neg h

/-- …yet merging them against the same third layer gives DIFFERENT layers.
So `merge` is not a function of the builders. THIS is the forcing theorem
position E owed; it is one `Handler.ext` away and was not taken. -/
private def isPure : Prog LayerSig Addr32 → Bool
  | .pure _ => true
  | .vis _ _ => false

private theorem left_at_A :
    ((LDesc.merge dProvidesA dOther).build ceF).handle (SvcE.ask "A")
      = Prog.op (S := LayerSig) (Sum.inl (SvcE.ask "A")) := rfl

private theorem right_at_A :
    ((LDesc.merge dProvidesNothing dOther).build ceF).handle (SvcE.ask "A")
      = (Prog.pure a1 : Prog LayerSig Addr32) := rfl

theorem merge_really_needs_the_content :
    (LDesc.merge dProvidesA dOther).build ceF
      ≠ (LDesc.merge dProvidesNothing dOther).build ceF := by
  intro h
  have hc : (Prog.op (S := LayerSig) (Sum.inl (SvcE.ask "A")))
      = (Prog.pure a1 : Prog LayerSig Addr32) := by
    rw [← left_at_A, ← right_at_A, h]
  have : false = true := congrArg isPure hc
  exact Bool.noConfusion this

/-! ## §D. The `fresh` nonce is semantically inert in this design.

Position E mints a `nonce` field on `fresh` (an address-moving change to
every stored `SystemNode`) and argues "the nonce is not a nicety; without
it the arm is unrepresentable."

But position E ALSO refuses memoization outright ("MEMOIZE — DOES NOT
BELONG, and there is no MemoMap parameter anywhere"). With no memo table,
nothing is ever shared, so there is nothing for `fresh` to defeat — and E's
own `build_fresh` discards the nonce. The two descriptions the nonce
separates have the SAME denotation: -/

def dAnyLeaf : LDesc := .leaf "A" [] 3

theorem fresh_nonce_separates_the_content :
    (LDesc.fresh 0 dAnyLeaf) ≠ (LDesc.fresh 1 dAnyLeaf) := by decide

/-- …but it buys nothing: the builder cannot see it. So E pays an
address-moving schema change for a field with no denotation. Position B
argues the same conclusion from the other side (`fresh` is a property of
the TRAVERSAL, not the key) and exhibits a build where the nonce is
genuinely unnecessary. -/
theorem fresh_nonce_is_semantically_inert (ce : CodeEnv) (m n : Nat) (d : LDesc) :
    (LDesc.fresh m d).build ce = (LDesc.fresh n d).build ce := rfl

end JudgeE

section Audit
#print axioms JudgeE.position_E_reacquires_per_use
#print axioms JudgeE.provide_reacquires_per_use
#print axioms JudgeE.one_use_acquires_once
#print axioms JudgeE.build_step_is_missing
#print axioms JudgeE.release_happens_before_the_second_use
#print axioms JudgeE.builds_agree
#print axioms JudgeE.merge_really_needs_the_content
#print axioms JudgeE.the_same_shape_holds_for_a_bool
#print axioms JudgeE.fresh_nonce_is_semantically_inert
#print axioms JudgeE.fresh_nonce_separates_the_content
end Audit
