import Effect4.Author
import Effect4.Run
import Effect4.Laws.Library.SynchronizedRef.Ops

/-! Public callers of the pure SynchronizedRef slice.
The finite observation contains the reply, backing value, and released semaphore fields.
R4 readers consume make_answers and modify_answers at a numeric body.
R10 readers consume the existing Ref model laws at that same pure body.
These controls establish no host execution, concurrency, waiting progress, or schedule agreement. -/

set_option autoImplicit false
set_option maxRecDepth 16384
namespace Test.Program.SynchronizedRef
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Modules
open Effect4.Schema Effect4.Schema.Model

step_context% Captures (amount : .nat)
abbrev Inputs : InputContext := ("current", .nat) :: Captures

def body : Step Inputs.types (.prod .nat .nat) :=
  step_inputs% Inputs => .pair current (.add current amount)

def capture (amount : TermSrc) : {t : Ty} → Input Captures.types t → TermSrc :=
  input_sources% (Captures) {amount := amount}

/-- Observe the backing value and each relevant released semaphore field. -/
def inspect (self reply : TermSrc) : Src NativeOp :=
  bindWith (Effect4.SynchronizedRef.get self) fun next =>
    bindWith (Ref.get (field self "semaphore")) fun lock =>
      succeed (tuple [reply, next, field lock "permits", field lock "taken",
        app "length" [field lock "waiters"], field lock "next"])

def numeric (name : String := "amount") : Src NativeOp :=
  bindName name (succeed (nat 2)) fun amount =>
    bindWith (Effect4.SynchronizedRef.make .nat (nat 5)) fun self =>
      bindWith (Effect4.SynchronizedRef.modify self body (capture amount)) fun reply =>
        inspect self reply

/-- These sources change their indices if resolved after a wrapper introduces locals. -/
def callerLast : TermSrc := fun env _ => .ok (.var (env.names.length - 1))
def callerPrevious : TermSrc := fun env _ => .ok (.var (env.names.length - 2))

def depthSensitive : Src NativeOp :=
  bindName "current" (succeed (nat 2)) fun _ =>
    bindWith (Effect4.SynchronizedRef.make .nat (nat 5)) fun self =>
      bindWith (Effect4.SynchronizedRef.modify callerLast body (capture callerPrevious)) fun reply =>
        inspect self reply

/-- Removing caller-scope freezing makes the same source observe wrapper locals. -/
def unfrozen : Src NativeOp :=
  bindName "current" (succeed (nat 2)) fun _ =>
    bindWith (Effect4.SynchronizedRef.make .nat (nat 5)) fun _ =>
      Semaphore.withPermits (field callerLast "semaphore") (nat 1)
        (Step.callback body (capture callerPrevious) (Ref.modifyWith (field callerLast "backing")))

/-- A captured term's own fold binders also move past the wrapper and callback slots. -/
def folded : Src NativeOp :=
  bindWith (Effect4.SynchronizedRef.make .nat (nat 5)) fun self =>
    bindWith (Effect4.SynchronizedRef.modify self body
      (capture (foldWith (app "cons" [nat 4, nilT]) (nat 0) (fun _ item => item)))) fun reply =>
      inspect self reply

step_context% StringCaptures (replacement : .string)
abbrev StringInputs : InputContext := ("current", .string) :: StringCaptures

def stringBody : Step StringInputs.types (.prod .string .string) :=
  step_inputs% StringInputs => .pair current replacement

def strings : Src NativeOp :=
  bindWith (succeed (ascribe .string (str "after"))) fun replacement =>
    bindWith (Effect4.SynchronizedRef.make .string (ascribe .string (str "before"))) fun self =>
      bindWith (Effect4.SynchronizedRef.modify self stringBody
        (input_sources% (StringCaptures) {replacement := replacement})) fun reply =>
          inspect self reply

abbrev handleValueTy : Ty := .deferredOf .nat .never
step_context% HandleCaptures (replacement : handleValueTy)
abbrev HandleInputs : InputContext := ("current", handleValueTy) :: HandleCaptures

def handleBody : Step HandleInputs.types (.prod .bool handleValueTy) :=
  step_inputs% HandleInputs => .pair (.sameDeferred current replacement) replacement

def handles : Src NativeOp :=
  bindWith (Deferred.make .nat .never) fun original =>
    bindWith (Deferred.make .nat .never) fun replacement =>
      bindWith (Effect4.SynchronizedRef.make handleValueTy original) fun self =>
        bindWith (Effect4.SynchronizedRef.modify self handleBody
          (input_sources% (HandleCaptures) {replacement := replacement})) fun reply =>
          bindWith (Effect4.SynchronizedRef.get self) fun next =>
            inspect self (tuple [reply, app "sameHandle" [next, replacement]])

def observation (src : Src NativeOp) : Option Val := do
  let b ← (Api.Author.program src).toOption
  match (Api.run b.program 2000).exit with
  | some (.success value) => some value
  | _ => none

def numericExpected (next : Nat) : Val :=
  Val.tuple [.nat 5, .nat next, .nat 1, .nat 0, .nat 0, .nat 0]

#guard observation (numeric "amount") == some (numericExpected 7)
#guard observation (numeric "current") == some (numericExpected 7)
#guard observation (numeric "acc") == some (numericExpected 7)
#guard observation depthSensitive == some (numericExpected 7)
#guard observation folded == some (numericExpected 9)
#guard observation strings == some (Val.tuple [.str "before", .str "after", .nat 1, .nat 0, .nat 0, .nat 0])
#guard observation handles == some (Val.tuple [Val.tuple [.bool false, .bool true],
  Value.promise 1, .nat 1, .nat 0, .nat 0, .nat 0])
#guard (Api.Author.program unfrozen).toOption.isNone
#guard observation (bindWith (Effect4.SynchronizedRef.make .nat (nat 5)) fun self =>
  inspect self (nat 41)) == some (Val.tuple [.nat 41, .nat 5, .nat 1, .nat 0, .nat 0, .nat 0])
#guard (do let b ← (Api.Author.program (Effect4.SynchronizedRef.make .nat (nat 5))).toOption
           Api.typeOf b.program) == some (EffTy.pure (Effect4.SynchronizedRef.handleTy .nat))
#guard (Api.Author.program (Effect4.SynchronizedRef.make .nat (str "wrong"))).toOption.isNone
#guard (Api.Author.program (Effect4.SynchronizedRef.get (nat 0))).toOption.isNone
#guard (Api.Author.program (bindWith (Ref.make (nat 5)) fun q =>
  Effect4.SynchronizedRef.modify q body (capture (nat 2)))).toOption.isNone
#guard (Api.Author.program (bindWith (Effect4.SynchronizedRef.make .nat (nat 5)) fun self =>
  Effect4.SynchronizedRef.modify self body (capture (str "wrong")))).toOption.isNone
#guard match (Effect4.SynchronizedRef.modify (nat 0) body
    (capture (fun _ path => .error ⟨path, .unbound "missing"⟩))) {} [8] with
  | .error refusal => refusal == ⟨[8], .unbound "missing"⟩
  | .ok _ => false
#guard Effect4.SynchronizedRef.buildingBlocks == ["Ref", "Semaphore"]

/-- A constructor reader checks the actual numeric constructor through existing Ref and Semaphore laws. -/
example (s : TypedScope) : Answers (nativeSignature [])
    (Effect4.SynchronizedRef.make .nat (nat 5)) s (Effect4.SynchronizedRef.handleTy .nat) :=
  Effect4.SynchronizedRef.make_answers rfl (nodesFormed_of_check (by decide))
    (fun _ => types_nat 5 false)

/-- A read reader checks the numeric backing field through the existing Ref rule. -/
example {self : TermSrc} {s : TypedScope}
    (typed : Typed (nativeSignature []) self s (Effect4.SynchronizedRef.handleTy .nat)) :
    Answers (nativeSignature []) (Effect4.SynchronizedRef.get self) s .nat :=
  Effect4.SynchronizedRef.get_answers rfl (nodesFormed_of_check (by decide)) typed

/-- A modify reader checks the actual callback and literal capture at the caller's handle scope. -/
example {self : TermSrc} {s : TypedScope}
    (typed : Typed (nativeSignature []) self s (Effect4.SynchronizedRef.handleTy .nat)) :
    Answers (nativeSignature []) (Effect4.SynchronizedRef.modify self body (capture (nat 2))) s .nat := by
  apply Effect4.SynchronizedRef.modify_answers body (capture (nat 2)) rfl
    (nodesFormed_of_check (by decide)) rfl (nodesFormed_of_check (by decide)) typed
  · intro t x
    cases x with
    | here => exact fun _ => types_nat 2
    | there _ x => nomatch x
  · exact ⟨⟨⟩, ⟨⟨⟩, ⟨⟩⟩⟩

/-- The backing read uses Ref.Model.get at a numeric allocated cell. -/
example (cell : Nat) {q : RefKey} {stores : Stores}
    (held : refPeek stores.refs q = some (.nat cell)) :
    syncOpStep (.refGet q) stores =
      some (Effect4.Ref.resultStores Store.Image.nat (Effect4.Ref.Model.get cell) q stores,
        .nat cell) := Effect4.Ref.get_agrees Store.Image.nat cell held

/-- The actual callback reads the independent old-value reply and arithmetic write.
This reader remains one backing operation; it states no wrapper or schedule agreement. -/
example (cell amount : Nat) {q : RefKey} {stores : Stores}
    (held : refPeek stores.refs q = some (.nat cell)) :
    ∃ term request,
      Step.callback body (capture (nat amount)) (Ref.modifyWith (var "r")) {names := ["r"]} [] =
        .ok (.perform (.refModifyWith term) request) ∧
      evalTerm [Val.cell q] request = some (Val.cell q) ∧
      syncOpStep (.refModify q term [Val.cell q]) stores =
        some (Effect4.Ref.resultStores (imageAt Leaves.refused .nat)
          (Effect4.Ref.Model.modify (fun (old : Nat) => (old, old + amount)) cell) q stores, .nat cell) := by
  apply Effect4.Ref.modify_callback_agrees (L := Leaves.refused) body (capture (nat amount))
    (amount, ()) (fun (old : Nat) => (old, old + amount)) cell rfl
  · intro t x
    cases x with
    | here => exact reads_nat amount _ _ _
    | there _ x => nomatch x
  · exact ⟨.var 0, rfl, rfl⟩
  · exact held
  · rfl
  · rfl

end Test.Program.SynchronizedRef
