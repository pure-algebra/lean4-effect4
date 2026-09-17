import Effect4.Codegen.Read
import Effect4.Codegen.SourceBindings
import Effect4.Api
import Effect4.Laws.Program.Hoisting
import Effect4.Laws.Program.HoistingTotal
import Effect4.Laws.Codegen.Module
import Effect4.Laws.Api.Codegen
import Test.Program.Gen

/-!
# Read contract — the reader against the printer, pinned

Plan: `docs/research/2026-09-04-a4-reader-plan.md`. One `#guard` per constructor of
`Effect4.Program.Eff` the printer accepts, per statement form, per `awaitFiber` mode, per
fork shape: the program prints, and what it prints reads back to it. Every pin is
`roundTrip sig spell n e = .ok e`, the executed shadow of `read_print`;
`read_exact` needs no pin of its own, since a round trip that lands on `e` printed `x` and
read it. Then one refusal pin per `ReadRefusal` constructor on a hand-built tree, and the two
things the printer loses, pinned as `readable = false` with the program the reader answers
instead.

The alphabet is `PrintContract`'s three rows plus `Ref.update` with its trailing `incr`,
so a trailing name is read back through `spell` on (spelling, trailing). `lawful` is the
receipt that this table meets `LawfulSpelling`, by `decide` on the finite alphabet wherever
the clause is decidable and by the byte lemma `Var.name_ne` where it quantifies over binders.

Everything a pin evaluates is inlined; the definitions below hold the alphabet only.
-/

namespace Test.Codegen.ReadContract

/-- The shared finite service profile retains the former lookup on every key,
including unknown codes and names reserved for the scheduler. -/
theorem nativeServiceTy_profile (key : Effect4.ServiceKey) :
    Effect4.Program.nativeServiceTy key =
      if key = Effect4.Program.nativeScopeKey then some Effect4.Program.Ty.scope
      else if key.name.value < Effect4.Machine.Env.firstFreeName then none
      else match key.service.value with
        | 4 => some .nat
        | 5 => some .bool
        | 6 => some .unit
        | 7 => some Effect4.Program.NativeOp.refTy
        | 8 => some Effect4.Program.NativeOp.sqlTy
        | 9 => some Effect4.Program.NativeOp.kvTy
        | _ => none := by
  by_cases h : key = Effect4.Program.nativeScopeKey
  · subst key
    rfl
  · have neq : (Effect4.Program.nativeScopeKey == key) = false := by
      exact beq_eq_false_iff_ne.mpr (Ne.symm h)
    simp only [Effect4.Program.nativeServiceTy, Effect4.Program.nativeReservedServiceTypes,
      List.find?, neq, if_neg h]
    split
    · rfl
    · generalize key.service.value = code
      match code with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | code + 10 => rfl

open Effect4.Program

/-- The four rows: a call row on a handle request, a value row, an async row, and a
read-modify-write row whose pure function trails the request. -/
def rowOf : Fin 4 → Row
  | 0 => ⟨"get", "Ref.get", .call, [], .sync, .handle "Ref.Ref<number>", .nat, .never, [],
           "Ref.ts:200", [], .deferred⟩
  | 1 => ⟨"count", "cell.count", .value, [], .sync, .unit, .nat, .never, [], "Ref.ts:210", [], .deferred⟩
  | 2 => ⟨"await", "Deferred.await", .call, [], .async,
           .handle "Deferred.Deferred<number, never>", .nat, .never, [], "Deferred.ts:120", [], .deferred⟩
  | 3 => ⟨"update", "Ref.update", .call, ["incr"], .sync, .handle "Ref.Ref<number>", .unit,
           .never, [], "Ref.ts:1273-1276", [], .deferred⟩

def sig : Signature (Fin 4) :=
  { rowOf := rowOf
  , atomOf := fun atom args => if atom = "succ" ∧ args = [Ty.nat] then some Ty.nat else none
  , scopeKey := ⟨⟨0⟩, ⟨0⟩⟩, serviceTy := fun _ => none }

/-- The inverse of the table on (spelling, trailing names). -/
def spell (s : String) (names : List String) : Option (Fin 4) :=
  if s = "Ref.get" ∧ names = [] then some 0
  else if s = "cell.count" ∧ names = [] then some 1
  else if s = "Deferred.await" ∧ names = [] then some 2
  else if s = "Ref.update" ∧ names = ["incr"] then some 3
  else none

theorem lawful : LawfulSpelling sig spell where
  spell_row := by decide
  row_of_spell := by
    intro s names op h
    unfold spell at h
    split at h
    · rename_i hc; cases h; exact ⟨hc.1.symm, hc.2.symm⟩
    · split at h
      · rename_i hc; cases h; exact ⟨hc.1.symm, hc.2.symm⟩
      · split at h
        · rename_i hc; cases h; exact ⟨hc.1.symm, hc.2.symm⟩
        · split at h
          · rename_i hc; cases h; exact ⟨hc.1.symm, hc.2.symm⟩
          · cases h
  value_trailing := by decide
  spelling_ne_name := by
    intro op i
    have h : ∀ op : Fin 4, (rowOf op).spelling.toByteArray.data.toList.head? ≠ some 97 := by
      decide
    exact (Var.name_ne (h op) i).symm
  spelling_not_reserved := by decide
  trailing_ne_name := by
    intro op i
    have h : ∀ op : Fin 4, ∀ s ∈ (rowOf op).trailing, s.toByteArray.data.toList.head? ≠ some 97 := by
      decide
    exact name_notin _ (h op) i
  trailing_ne_undefined := by decide

/-! ## Tuple-call rows: the canonical wrapper, scoping and trailing-name order

The fixture shares one export spelling between a synchronous row without trailing
names and an asynchronous row with two trailing names. It exercises the generic
reader independently of the native table. -/

/-! ## `E4-CHECK-CE-013`: a row's declared type arguments

rc.112's `Deferred.make` has defaulted type parameters, so a bare call types the handle at
those defaults and every later use is rejected. A row that declares type arguments prints and
reads them, and only them: a bare call of that row and a call carrying the wrong arguments
are both outside the readable image. -/

def genericSig : Signature Bool :=
  { rowOf := fun _ =>
      ⟨"make", "Deferred.make", .call, [], .sync, .unit,
        .handle "Deferred.Deferred<number, number>", .never, [], "vendor/effect-4.0.0-rc.112/src/Deferred.ts:171",
        ["number", "number"], .deferred⟩
  , atomOf := fun _ _ => none, scopeKey := ⟨⟨0⟩, ⟨0⟩⟩, serviceTy := fun _ => none }

def genericSpell (s : String) (names : List String) : Option Bool :=
  if s = "Deferred.make" ∧ names = [] then some true else none

-- the printed head carries the declared arguments, and reads back to the row
#guard (printRow (genericSig.rowOf true) (.lit .unit)).map
  (TypeScript.Render.expr TypeScript.house0 0) = .ok "Deferred.make<number, number>()"

#guard roundTrip genericSig genericSpell 0 (.perform true (.lit .unit))
  = .ok (.perform true (.lit .unit))

-- the bare call names this row but omits what it declares, so it is refused rather than
-- read as some other program: `Deferred.make()` is exactly the emission `E4-CHECK-CE-013`
-- rejects
#guard (readEff genericSig genericSpell 0 (.call (.ident "Deferred.make") [])).isOk = false

-- wrong type arguments, and an empty argument list, are refused
#guard (readEff genericSig genericSpell 0
  (.call (.generic (.ident "Deferred.make") [.name ["number"] []]) [])).isOk = false
#guard (readEff genericSig genericSpell 0
  (.call (.generic (.ident "Deferred.make") []) [])).isOk = false

-- and a row that declares none still refuses a call that carries some
#guard (readEff sig spell 1
  (.call (.generic (.ident "Ref.get") [.name ["number"] []]) [.ident "a0"])).isOk = false

def tupleRowOf : Bool → Row
  | false => ⟨"tuple", "Fixture.tuple", .tupleCall, [], .sync,
      .prod .nat .nat, .nat, .never, [], "§14 tuple-call fixture", [], .deferred⟩
  | true => ⟨"tupleAsync", "Fixture.tuple", .tupleCall, ["first", "second"], .async,
      .prod .nat .nat, .nat, .never, [], "§14 tuple-call fixture with trailing names", [], .deferred⟩

def tupleSig : Signature Bool :=
  { rowOf := tupleRowOf, atomOf := fun _ _ => none, scopeKey := ⟨⟨0⟩, ⟨0⟩⟩
  , serviceTy := fun _ => none }

def tupleSpell (s : String) (names : List String) : Option Bool :=
  if s = "Fixture.tuple" ∧ names = [] then some false
  else if s = "Fixture.tuple" ∧ names = ["first", "second"] then some true
  else none

theorem tupleLawful : LawfulSpelling tupleSig tupleSpell where
  spell_row := by decide
  row_of_spell := by
    intro s names op h
    unfold tupleSpell at h
    split at h
    · rename_i hc; cases h; exact ⟨hc.1.symm, hc.2.symm⟩
    · split at h
      · rename_i hc; cases h; exact ⟨hc.1.symm, hc.2.symm⟩
      · cases h
  value_trailing := by decide
  spelling_ne_name := by
    intro op i
    cases op <;> exact (Var.name_ne (by decide) i).symm
  spelling_not_reserved := by decide
  trailing_ne_name := by
    intro op i
    cases op <;> exact name_notin _ (by decide) i
  trailing_ne_undefined := by decide

-- The wrapper head is gone: `Reflect.apply` is an ordinary unknown atom (source-repairs §18).
#guard headOf "Reflect.apply" = none

#guard roundTrip tupleSig tupleSpell 1 (.perform false (.var 0)) =
  .ok (.perform false (.var 0))

#guard roundTrip tupleSig tupleSpell 1 (.perform true (.var 0)) =
  .ok (.perform true (.var 0))

#guard roundTrip tupleSig tupleSpell 0
    (.perform false (.app "pair" (.cons (.lit (.nat 2)) (.cons (.lit (.nat 7)) .nil)))) =
  .ok (.perform false (.app "pair" (.cons (.lit (.nat 2)) (.cons (.lit (.nat 7)) .nil))))

#guard roundTrip tupleSig tupleSpell 1
    (.perform true (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 7)) .nil)))) =
  .ok (.perform true (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 7)) .nil))))

-- A pair of one variable's components prints as the variable and reads back as it:
-- outside the readable image, by `requestReadable`.
#guard requestReadable (tupleRowOf false) 1
    (.app "pair" (.cons (.app "fst" (.cons (.var 0) .nil))
      (.cons (.app "snd" (.cons (.var 0) .nil)) .nil))) = false

#guard roundTrip tupleSig tupleSpell 1
    (.perform false (.app "pair" (.cons (.app "fst" (.cons (.var 0) .nil))
      (.cons (.app "snd" (.cons (.var 0) .nil)) .nil)))) = .ok (.perform false (.var 0))

-- Tuple rows retain their request; request metadata does not introduce a new loss.
#guard requestReadable { tupleRowOf false with request := .unit } 1 (.var 0) = true

#guard requestReadable (tupleRowOf false) 1 (.var 1) = false
-- `undefined` prints as one identifier, like a binder, so its component reads read back.
#guard requestReadable (tupleRowOf false) 1 (.lit .unit) = true
#guard roundTrip tupleSig tupleSpell 1 (.perform false (.lit .unit)) =
  .ok (.perform false (.lit .unit))
#guard requestReadable (tupleRowOf false) 1 (.lit (.nat 7)) = false
#guard requestReadable (tupleRowOf false) 1
    (.app "pair" (.cons (.var 0) (.cons (.var 1) .nil))) = false

-- The saved-variable spelling reads as the variable, under the ordinary scope check.
#guard readEff tupleSig tupleSpell 1 (.call (.ident "Fixture.tuple")
    [.call (.ident "fst") [.ident "a1"], .call (.ident "snd") [.ident "a1"]]) =
  .error (.unknownIdent "a1")

#guard readEff tupleSig tupleSpell 1 (.call (.ident "Fixture.tuple")
    [.call (.ident "fst") [.ident "a0"], .call (.ident "snd") [.ident "a0"],
      .ident "first", .ident "second"]) =
  .ok (.perform true (.var 0))

-- Components of two different identifiers are an ordinary pair.
#guard readEff tupleSig tupleSpell 2 (.call (.ident "Fixture.tuple")
    [.call (.ident "fst") [.ident "a0"], .call (.ident "snd") [.ident "a1"]]) =
  .ok (.perform false (.app "pair" (.cons (.app "fst" (.cons (.var 0) .nil))
    (.cons (.app "snd" (.cons (.var 1) .nil)) .nil))))

#guard readEff tupleSig tupleSpell 1 (.call (.ident "Fixture.tuple") [.ident "a0", .int 7]) =
  .ok (.perform false (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 7)) .nil))))

-- Trailing names are matched exactly and in order: a misordered suffix is no row, and a call
-- that is no row and no head is refused by its head (since DI-72 it is no atom application).
#guard readEff tupleSig tupleSpell 1 (.call (.ident "Fixture.tuple")
    [.ident "a0", .int 7, .ident "second", .ident "first"]) =
  .error (.unknownHead "Fixture.tuple")

-- The former one-request call, a one-argument call with trailing names, and three
-- plain arguments are not tuple readings.
#guard readEff tupleSig tupleSpell 1 (.call (.ident "Fixture.tuple") [.ident "a0"]) =
  .error (.arity "Fixture.tuple")

#guard readEff tupleSig tupleSpell 1 (.call (.ident "Fixture.tuple")
    [.ident "a0", .ident "first", .ident "second"]) = .error (.arity "Fixture.tuple")

-- three plain arguments are no row call, and since DI-72 no atom application either
#guard readEff tupleSig tupleSpell 1 (.call (.ident "Fixture.tuple") [.ident "a0", .int 7, .int 8]) =
  .error (.unknownHead "Fixture.tuple")

-- A call row does not accept the tuple reading.
#guard readEff sig spell 1 (.call (.ident "Ref.get") [.ident "a0", .int 1]) =
  .error (.arity "Ref.get")

-- The former wrapper is a call whose head is no reserved name and no row: refused before its
-- arguments are read.
#guard readEff tupleSig tupleSpell 1 (.call (.ident "Reflect.apply")
    [.ident "Fixture.tuple", .ident "undefined", .ident "a0"]) =
  .error (.unknownHead "Reflect.apply")

#guard readEff tupleSig tupleSpell 0 (.ident "Reflect.apply") =
  .error (.unknownIdent "Reflect.apply")

-- Every old native one-request tuple call is rejected by the row parser.
#guard [NativeOp.refSet, .refGetAndSet, .refSetAndGet, .deferredSucceed, .deferredFail].all
    fun op => decide (readEff nativeSignature nativeSpell 1
      (.call (.ident op.row.spelling)
        [.call (.ident "pair") [.ident "a0", .int 7]]) = .error (.arity op.row.spelling))

#guard [NativeOp.refSet, .refGetAndSet, .refSetAndGet, .deferredSucceed, .deferredFail].all
    fun op => decide (roundTrip nativeSignature nativeSpell 1
      (.perform op (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 7)) .nil)))) =
      .ok (.perform op (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 7)) .nil)))))

-- A native request tuple may pass through a bound variable before the call.
open Effect4.Api in
#guard roundTrip
    (.bind (.perform .deferredMake (.lit .unit))
      (.bind (.succeed (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 7)) .nil))))
        (.perform .deferredSucceed (.var 1)))) =
  .ok (.bind (.perform .deferredMake (.lit .unit))
    (.bind (.succeed (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 7)) .nil))))
      (.perform .deferredSucceed (.var 1))))

/-! ## Exits, thunks and rows -/

#guard roundTrip sig spell 0 (.succeed (.lit (.nat 1)))
  = .ok (.succeed (.lit (.nat 1)))

#guard roundTrip sig spell 0 (.fail (.lit (.str "boom")))
  = .ok (.fail (.lit (.str "boom")))

#guard roundTrip sig spell 0 (.failCause (.both (.fail (.lit (.str "l")))
      (.both (.die (.lit (.nat 2))) (.both (.interrupt none) (.interrupt (some (.lit (.nat 7))))))))
  = .ok (.failCause (.both (.fail (.lit (.str "l")))
      (.both (.die (.lit (.nat 2))) (.both (.interrupt none) (.interrupt (some (.lit (.nat 7))))))))

-- DI-72 (2026-09-13), then the `Eff` series: `yieldError e` printed as `Effect.fail(e)`, the
-- failure it meant, and retired into `fail`. `fail` reads back as itself, and a bare value in
-- effect position is a tree the printer never emits.
#guard roundTrip sig spell 1 (.fail (.var 0)) = .ok (.fail (.var 0))

#guard roundTrip sig spell 0 (.fail (.lit .unit)) = .ok (.fail (.lit .unit))

#guard roundTrip sig spell 0 (.fail (.lit (.nat 3))) = .ok (.fail (.lit (.nat 3)))

#guard roundTrip sig spell 1 (.fail (.app "succ" (.cons (.var 0) .nil)))
  = .ok (.fail (.app "succ" (.cons (.var 0) .nil)))

#guard readable sig spell 1 (.fail (.var 0)) = true
#guard readable sig spell 0 (.fail (.lit (.nat 3))) = true
#guard readEff sig spell 0 (.int 3) = .error (.shape "bare value")
#guard readEff sig spell 0 (.str "hi") = .error (.shape "bare value")
#guard readEff sig spell 0 (.ident "undefined") = .error (.shape "bare value")
#guard readEff sig spell 1 (.ident "a0") = .error (.shape "bare binder")
#guard readEff sig spell 1 (.call (.ident "succ") [.ident "a0"]) = .error (.unknownHead "succ")

#guard roundTrip sig spell 1 (.sync (.app "succ" (.cons (.var 0) .nil)))
  = .ok (.sync (.app "succ" (.cons (.var 0) .nil)))

#guard roundTrip sig spell 0 (.suspend (.succeed (.lit .unit)))
  = .ok (.suspend (.succeed (.lit .unit)))

#guard roundTrip sig spell 1 (.perform 0 (.var 0)) = .ok (.perform 0 (.var 0))

#guard roundTrip sig spell 0 (.perform 1 (.lit .unit))
  = .ok (.perform 1 (.lit .unit))

#guard roundTrip sig spell 1 (.perform 3 (.var 0)) = .ok (.perform 3 (.var 0))

#guard roundTrip sig spell 1 (.perform 2 (.var 0)) = .ok (.perform 2 (.var 0))

/-! ## Sequencing -/

#guard roundTrip sig spell 0 (.bind (.succeed (.lit (.nat 1))) (.succeed (.var 0)))
  = .ok (.bind (.succeed (.lit (.nat 1))) (.succeed (.var 0)))

#guard roundTrip sig spell 1 (.gen (.cons (.bindYield (.perform 0 (.var 0)))
      (.cons (.yieldDiscard (.succeed (.var 1)))
      (.cons (.ifElse (.lit (.bool true))
        (.cons (.bindYield (.succeed (.lit (.nat 1)))) .nil)
        (.cons (.yieldDiscard (.succeed (.lit .unit))) .nil))
      (.cons (.whileTrue (.cons (.yieldDiscard (.succeed (.lit (.nat 1)))) (.cons .breakLoop .nil)))
      (.cons (.ret (.var 1)) .nil))))))
  = .ok (.gen (.cons (.bindYield (.perform 0 (.var 0)))
      (.cons (.yieldDiscard (.succeed (.var 1)))
      (.cons (.ifElse (.lit (.bool true))
        (.cons (.bindYield (.succeed (.lit (.nat 1)))) .nil)
        (.cons (.yieldDiscard (.succeed (.lit .unit))) .nil))
      (.cons (.whileTrue (.cons (.yieldDiscard (.succeed (.lit (.nat 1)))) (.cons .breakLoop .nil)))
      (.cons (.ret (.var 1)) .nil))))))

#guard roundTrip sig spell 0 (.gen .nil) = .ok (.gen .nil)

/-! ## Failure, exit and the masks -/

#guard roundTrip sig spell 0 (.catchCause (.succeed (.lit (.nat 1))) (.succeed (.var 0)))
  = .ok (.catchCause (.succeed (.lit (.nat 1))) (.succeed (.var 0)))

#guard roundTrip sig spell 0 (.matchCause (.succeed (.lit (.nat 1))) (.succeed (.var 0))
      (.failCause (.fail (.var 0))))
  = .ok (.matchCause (.succeed (.lit (.nat 1))) (.succeed (.var 0)) (.failCause (.fail (.var 0))))

#guard roundTrip sig spell 0 (.onExit (.succeed (.lit (.nat 1))) (.succeed (.var 0)))
  = .ok (.onExit (.succeed (.lit (.nat 1))) (.succeed (.var 0)))

#guard roundTrip sig spell 0 (.exit (.succeed (.lit (.nat 1))))
  = .ok (.exit (.succeed (.lit (.nat 1))))

#guard roundTrip sig spell 0 (.uninterruptible (.succeed (.lit (.nat 1))))
  = .ok (.uninterruptible (.succeed (.lit (.nat 1))))

#guard roundTrip sig spell 0 (.interruptible (.succeed (.lit (.nat 1))))
  = .ok (.interruptible (.succeed (.lit (.nat 1))))

/-! ## Control by value, scheduling and parking -/

#guard roundTrip sig spell 0 (.select (.lit (.bool true)) .bool (.succeed (.lit (.nat 1)))
      (.succeed (.lit .unit)))
  = .ok (.select (.lit (.bool true)) .bool (.succeed (.lit (.nat 1))) (.succeed (.lit .unit)))

#guard roundTrip sig spell 0 (.yieldNow 2) = .ok (.yieldNow 2)

#guard roundTrip sig spell 1 (.awaitFiber (.var 0) .joinEffect)
  = .ok (.awaitFiber (.var 0) .joinEffect)

#guard roundTrip sig spell 1 (.awaitFiber (.var 0) .awaitValue)
  = .ok (.awaitFiber (.var 0) .awaitValue)

/-! ## Scopes -/

#guard roundTrip sig spell 0 (.scoped (.succeed (.lit (.nat 1))))
  = .ok (.scoped (.succeed (.lit (.nat 1))))

#guard roundTrip sig spell 0 (.acquireRelease (.succeed (.lit (.nat 1))) (.succeed (.var 1)))
  = .ok (.acquireRelease (.succeed (.lit (.nat 1))) (.succeed (.var 1)))

#guard roundTrip sig spell 2 (.withFiber (.closeScope (.var 0) (.var 1)))
  = .ok (.withFiber (.closeScope (.var 0) (.var 1)))

/-! ## `withFiber`: the fork family, both `daemon` values and all three masks -/

#guard roundTrip sig spell 0 (.withFiber (.fork (.succeed (.lit (.nat 1))) ⟨true, false, .interruptible⟩))
  = .ok (.withFiber (.fork (.succeed (.lit (.nat 1))) ⟨true, false, .interruptible⟩))

#guard roundTrip sig spell 0 (.withFiber (.fork (.succeed (.lit (.nat 1))) ⟨false, false, .uninterruptible⟩))
  = .ok (.withFiber (.fork (.succeed (.lit (.nat 1))) ⟨false, false, .uninterruptible⟩))

#guard roundTrip sig spell 0 (.withFiber (.fork (.succeed (.lit (.nat 1))) ⟨true, false, .inherit⟩))
  = .ok (.withFiber (.fork (.succeed (.lit (.nat 1))) ⟨true, false, .inherit⟩))

#guard roundTrip sig spell 0 (.withFiber (.fork (.succeed (.lit (.nat 1))) ⟨true, true, .interruptible⟩))
  = .ok (.withFiber (.fork (.succeed (.lit (.nat 1))) ⟨true, true, .interruptible⟩))

#guard roundTrip sig spell 0 (.withFiber (.fork (.succeed (.lit (.nat 1))) ⟨false, true, .uninterruptible⟩))
  = .ok (.withFiber (.fork (.succeed (.lit (.nat 1))) ⟨false, true, .uninterruptible⟩))

#guard roundTrip sig spell 0 (.withFiber (.fork (.succeed (.lit (.nat 1))) ⟨true, true, .inherit⟩))
  = .ok (.withFiber (.fork (.succeed (.lit (.nat 1))) ⟨true, true, .inherit⟩))

-- `Effect.forkIn` and `Effect.forkScoped` fork a *daemon* in rc.112
-- (`internal/effect.ts:5366` passes `true` for `forkUnsafe`'s `daemon`, `:5264-5269`;
-- `:5406` routes `forkScoped` through `forkIn`), so that is the image they read back into
-- and round-trip on (`E4-CHECK-CE-015`).
#guard roundTrip sig spell 1 (.withFiber (.forkIn (.succeed (.lit (.nat 1))) ⟨true, true, .inherit⟩ (.var 0)))
  = .ok (.withFiber (.forkIn (.succeed (.lit (.nat 1))) ⟨true, true, .inherit⟩ (.var 0)))

#guard roundTrip sig spell 0 (.withFiber (.forkScoped (.succeed (.lit (.nat 1))) ⟨true, true, .interruptible⟩))
  = .ok (.withFiber (.forkScoped (.succeed (.lit (.nat 1))) ⟨true, true, .interruptible⟩))

/-! ## `withFiber`: the handle actions -/

#guard roundTrip sig spell 2 (.withFiber (.runIn (.var 0) (.var 1)))
  = .ok (.withFiber (.runIn (.var 0) (.var 1)))

-- The runIn adapter adds no binder to either source term's lexical environment.
#guard roundTrip sig spell 2 (.bind (.succeed (.var 0))
    (.withFiber (.runIn (.var 2) (.var 1)))) =
  .ok (.bind (.succeed (.var 0)) (.withFiber (.runIn (.var 2) (.var 1))))

#guard headOf "Effect.withFiber" = some .withFiber

#guard readEff sig spell 2 (.call (.ident "Effect.withFiber")
    [.arrowBlock [] [.exprStmt (.call (.ident "Fiber.runIn") [.ident "a0", .ident "a1"]),
      .ret (.ident "Effect.void")]]) = .ok (.withFiber (.runIn (.var 0) (.var 1)))

#guard readEff sig spell 2 (.call (.ident "Fiber.runIn") [.ident "a0", .ident "a1"]) =
  .error (.arity "Fiber.runIn")

#guard readEff sig spell 2 (.call (.ident "Effect.withFiber")
    [.arrowBlock ["a2"] [.exprStmt (.call (.ident "Fiber.runIn") [.ident "a0", .ident "a1"]),
      .ret (.ident "Effect.void")]]) = .error (.shape "runIn")

#guard readEff sig spell 2 (.call (.ident "Effect.withFiber")
    [.arrowBlock [] [.exprStmt (.call (.ident "Fiber.runIn") [.ident "a0", .ident "a1"]),
      .exprStmt (.ident "extra"), .ret (.ident "Effect.void")]]) = .error (.shape "runIn")

#guard readEff sig spell 2 (.call (.ident "Effect.withFiber")
    [.arrowBlock [] [.exprStmt (.call (.ident "Fiber.runIn") [.ident "a0", .ident "a1"]),
      .ret (.ident "undefined")]]) = .error (.shape "runIn")

#guard readEff sig spell 2 (.call (.ident "Effect.withFiber")
    [.arrowBlock [] [.exprStmt (.call (.ident "Fiber.runIn") [.ident "a0", .ident "a1"]),
      .ret (.call (.ident "Effect.succeed") [.ident "undefined"])]]) = .error (.shape "runIn")

#guard readEff sig spell 2 (.call (.ident "Effect.withFiber")
    [.arrowBlock [] [.exprStmt (.call (.ident "Fiber.other") [.ident "a0", .ident "a1"]),
      .ret (.ident "Effect.void")]]) = .error (.shape "runIn")

#guard readEff sig spell 2 (.call (.ident "Effect.withFiber")
    [.arrow none (.call (.ident "Fiber.runIn") [.ident "a0", .ident "a1"])]) =
  .error (.shape "runIn")

#guard readEff sig spell 0 (.call (.ident "Effect.withFiber")
    [.arrowBlock [] [.exprStmt (.call (.ident "Fiber.runIn") [.ident "a0", .ident "a1"]),
      .ret (.ident "Effect.void")]]) = .error (.unknownIdent "a0")

#guard roundTrip sig spell 1 (.withFiber (.interrupt (.var 0)))
  = .ok (.withFiber (.interrupt (.var 0)))

#guard roundTrip sig spell 1 (.withFiber (.interruptAll (.var 0) none))
  = .ok (.withFiber (.interruptAll (.var 0) none))

#guard roundTrip sig spell 2 (.withFiber (.interruptAll (.var 0) (some (.var 1))))
  = .ok (.withFiber (.interruptAll (.var 0) (some (.var 1))))

#guard roundTrip sig spell 1 (.withFiber (.awaitAll (.var 0)))
  = .ok (.withFiber (.awaitAll (.var 0)))

#guard roundTrip sig spell 0 (.withFiber (.raceAll (.cons (.succeed (.lit (.nat 1)))
      (.cons (.succeed (.lit .unit)) .nil))))
  = .ok (.withFiber (.raceAll (.cons (.succeed (.lit (.nat 1))) (.cons (.succeed (.lit .unit)) .nil))))

#guard roundTrip sig spell 0 (.withFiber .getContext) = .ok (.withFiber .getContext)

#guard roundTrip sig spell 0 (.withFiber .getId) = .ok (.withFiber .getId)

/-! ## The refusals, one per constructor of `ReadRefusal` -/

#guard readEff sig spell 0 (.call (.ident "Cause.fail") [.int 1]) = .error (.unknownHead "Cause.fail")

#guard readEff sig spell 0 (.ident "nope") = .error (.unknownIdent "nope")

#guard readEff sig spell 0 (.ident "Ref.get") = .error (.arity "Ref.get")

#guard readEff sig spell 0 (.call (.ident "Effect.flatMap")
    [.call (.ident "Effect.succeed") [.int 1], .lambda ["b0"] (.ident "b0")])
  = .error (.binder "a0")

#guard readEff sig spell 0 (.call (.ident "Effect.forkChild")
    [.call (.ident "Effect.succeed") [.int 1], .object []])
  = .error (.shape "forkOptions")

#guard readEff sig spell 0 (.int (-1)) = .error (.negative (-1))

#guard readEff sig spell 0 (.call (.ident "Effect.gen") [.generator [.letDefinite "x" (.name ["number"] [])]])
  = .error .unsupportedStmt

/-! ## Explicit annotations are retained at the carrier boundary

The raw reader accepts the printer's unannotated local image. It refuses
annotations here instead of dropping source evidence before checked ingestion,
and it names the refusal `annotation` with the position: an annotation is not an
argument list the row table does not print (`arity`) and not a statement form with
no reading (`unsupportedStmt`), and a consumer routing on the alphabet must be able
to tell "annotated, not admitted here" from "wrong shape".
-/

#guard readEff nativeSignature nativeSpell 0
    (.call (.ident "Effect.sync") [.arrow (some (.name ["number"] [])) (.int 1)]) =
  .error (.annotation "Effect.sync thunk return")
#guard readEff nativeSignature nativeSpell 0
    (.call (.ident "Effect.suspend") [.arrow (some (.name ["number"] []))
      (.call (.ident "Effect.succeed") [.int 1])]) =
  .error (.annotation "Effect.suspend thunk return")
#guard readEff nativeSignature nativeSpell 0
    (.call (.ident "Effect.flatMap") [.call (.ident "Effect.succeed") [.int 1],
      .lambda [⟨"a0", some (.name ["number"] [])⟩]
        (.call (.ident "Effect.succeed") [.ident "a0"]) none]) =
  .error (.annotation "Effect.flatMap parameter")
#guard readEff nativeSignature nativeSpell 0
    (.call (.ident "Effect.flatMap") [.call (.ident "Effect.succeed") [.int 1],
      .lambda [⟨"a0", none⟩] (.call (.ident "Effect.succeed") [.ident "a0"])
        (some (.name ["number"] []))]) =
  .error (.annotation "Effect.flatMap return")
#guard readEff nativeSignature nativeSpell 0
    (.call (.ident "Effect.gen") [.generator
      [.constYield "a0" (.call (.ident "Effect.succeed") [.int 1])
        (some (.name ["number"] [])), .ret (.ident "a0")]]) =
  .error (.annotation "yielded const")
#guard readEff nativeSignature nativeSpell 0
    (.call (.ident "Effect.gen") [.generator
      [.letInit "a0" (.int 1) (some (.name ["number"] [])), .ret (.ident "a0")]]) =
  .error (.annotation "local const")
-- The two refusals the new constructor must not swallow: an argument list no arm reads,
-- and a statement form with no reading at all.
#guard readEff nativeSignature nativeSpell 2
    (.call (.ident "Fiber.runIn") [.ident "a0", .ident "a1"]) =
  .error (.arity "Fiber.runIn")
#guard readEff nativeSignature nativeSpell 0
    (.call (.ident "Effect.gen") [.generator [.letDefinite "x" (.name ["number"] [])]]) =
  .error .unsupportedStmt

#print axioms Effect4.Program.annotationSite
#print axioms Effect4.Program.callRefusal
#print axioms Effect4.Program.stmtRefusal
#guard roundTrip nativeSignature nativeSpell 0
    (.bind (.succeed (.lit (.nat 1))) (.succeed (.var 0))) =
  .ok (.bind (.succeed (.lit (.nat 1))) (.succeed (.var 0)))

/-! ## What the printer loses

A `daemon` flag on a scoped fork has no field in the options object; a `perform` on an
`.async` row and a `callback` on a `.sync` row print like the row's declared kind; the request
of a `unit`-request row or a value row is dropped. Each is `readable = false`, and the reader
answers the program the printer kept. -/

-- The retained negative: a *non-daemon* `forkIn`/`forkScoped` action has no rc.112 spelling,
-- so it is outside the readable image and the reader answers the daemon program the printed
-- text means. The refusal is kept, only its side is the source's (`E4-CHECK-CE-015`).
#guard readable sig spell 0 (.withFiber (.forkScoped (.succeed (.lit (.nat 1))) ⟨true, false, .inherit⟩))
  = false

#guard roundTrip sig spell 0 (.withFiber (.forkScoped (.succeed (.lit (.nat 1))) ⟨true, false, .inherit⟩))
  = .ok (.withFiber (.forkScoped (.succeed (.lit (.nat 1))) ⟨true, true, .inherit⟩))

#guard readable sig spell 1 (.withFiber (.forkIn (.succeed (.lit (.nat 1))) ⟨true, false, .inherit⟩ (.var 0)))
  = false

#guard roundTrip sig spell 1 (.withFiber (.forkIn (.succeed (.lit (.nat 1))) ⟨true, false, .inherit⟩ (.var 0)))
  = .ok (.withFiber (.forkIn (.succeed (.lit (.nat 1))) ⟨true, true, .inherit⟩ (.var 0)))

#guard readable sig spell 0 (.perform 1 (.lit (.nat 5))) = false

#guard roundTrip sig spell 0 (.perform 1 (.lit (.nat 5))) = .ok (.perform 1 (.lit .unit))

#guard readable sig spell 0 (.fail (.var 3)) = false

/-! ## The native profile through `Api`: trailing names and the two `Scope.make` rows -/

open Effect4.Api in
#guard roundTrip (.bind (.perform .refMake (.lit (.nat 0))) (.perform (.refUpdate .double) (.var 0)))
  = .ok (.bind (.perform .refMake (.lit (.nat 0))) (.perform (.refUpdate .double) (.var 0)))

open Effect4.Api in
#guard roundTrip (.bind (.perform (.scopeMake .parallel) (.lit .unit))
    (.perform (.scopeMake .sequential) (.lit .unit)))
  = .ok (.bind (.perform (.scopeMake .parallel) (.lit .unit)) (.perform (.scopeMake .sequential) (.lit .unit)))

open Effect4.Api in
#guard roundTrip (.bind (.perform .deferredMake (.lit .unit)) (.perform .deferredAwait (.var 0)))
  = .ok (.bind (.perform .deferredMake (.lit .unit)) (.perform .deferredAwait (.var 0)))
-- the timer (A4): `Effect.sleep(5)` is the async row's callback, `Effect.currentTimeMillis`
-- the value row
open Effect4.Api in
#guard roundTrip (.bind (.perform .sleep (.lit (.nat 5))) (.perform .clockNow (.lit .unit)))
  = .ok (.bind (.perform .sleep (.lit (.nat 5))) (.perform .clockNow (.lit .unit)))

/-! ## The corpus: every program the generator writes, through `Api.print` and `Api.read`

`Test/Program/Gen.lean` is the seeded generator of the image-parser spike
(`docs/research/2026-09-05-image-parser-spike.md`): 400 programs at depth 4 over every
constructor the printer accepts. Four pins: how many are `readable` (the generator draws a
request for every row, so a `unit`-request row loses it; a scoped fork with `daemon` loses
that); every readable one comes back as itself (`read_print`, executed); every one of the 400
that holds no loop comes back as a program that prints the same tree (`read_exact`, executed),
and the ones that hold a loop are refused (`iterate` is read back at R5); and no unreadable
one comes back unchanged, so on this corpus `readable` is exact, not merely sufficient. -/

#guard (Test.Program.Gen.corpus 400 4).length = 400

-- Which programs are readable is the committed corpus index (`generated/corpus-index.tsv`,
-- one row per program, held by `make check-gen`), not a count pinned here; the law below is
-- the property: a readable program comes back as itself.
#guard (Test.Program.Gen.corpus 400 4).all fun p =>
  !Effect4.Api.readable p || decide (Effect4.Api.roundTrip p = .ok p)

/-- Whether a program holds a loop anywhere. `iterate` prints and is read back at R5, so until
then the hand reader refuses the image of any program that holds one. -/
private def holdsLoop (p : Eff NativeOp) : Bool :=
  foldMap_eff false (· || ·) p (f_eff := fun | .iterate .. => true | _ => false)

#guard (Test.Program.Gen.corpus 400 4).all fun p =>
  match Effect4.Api.roundTrip p with
  | .ok q => (Effect4.Api.print q).toOption == (Effect4.Api.print p).toOption
  | .error _ => holdsLoop p

-- The refusals are exactly the loops: R5 turns this pin into the guard above with no
-- `.error` arm.
#guard (Test.Program.Gen.corpus 400 4).all fun p =>
  holdsLoop p == !(Effect4.Api.roundTrip p).toOption.isSome

#guard ((Test.Program.Gen.corpus 400 4).filter fun p =>
  !Effect4.Api.readable p && decide (Effect4.Api.roundTrip p = .ok p)).length = 0

/-! ## The join: keys and all eight layer forms

Layer effects have their own empty environment, even when provision occurs below
an outer binder. The service-key tests retain both numbers and the exact type.
-/

private def joinKey : Effect4.ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
private def joinValue : Eff NativeOp := .succeed (.lit (.nat 7))
private def joinLayers : List (LayerTerm NativeOp) :=
  [ .succeed joinKey (.nat 7)
  , .effect joinKey joinValue
  , .effectDiscard joinValue
  , .provide (.effect joinKey joinValue) (.succeed joinKey (.nat 8))
  , .provideMerge (.effect joinKey joinValue) (.succeed joinKey (.nat 8))
  , .merge (.succeed joinKey (.nat 7)) (.succeed ⟨⟨5⟩, ⟨5⟩⟩ (.bool true))
  , .fresh (.effect joinKey joinValue)
  , .orDie (.effect joinKey joinValue) ]

#guard roundTrip nativeSignature nativeSpell 0 (.service joinKey) = .ok (.service joinKey)
#guard roundTrip nativeSignature nativeSpell 0
  (.provideService joinKey (.lit (.nat 7)) (.service joinKey)) =
  .ok (.provideService joinKey (.lit (.nat 7)) (.service joinKey))
#guard joinLayers.length = 8
#guard joinLayers.all fun layer => [false, true].all fun isLocal =>
  let program := Eff.provideLayer layer isLocal (.service joinKey)
  readable nativeSignature nativeSpell 0 program &&
    decide (roundTrip nativeSignature nativeSpell 0 program = .ok program)
#guard roundTrip nativeSignature nativeSpell 0
  (.bind joinValue (.provideLayer
    (.effect joinKey (.bind joinValue (.succeed (.var 0)))) true (.succeed (.var 0)))) =
  .ok (.bind joinValue (.provideLayer
    (.effect joinKey (.bind joinValue (.succeed (.var 0)))) true (.succeed (.var 0))))

#guard [Effect4.ServiceKey.mk ⟨0⟩ ⟨0⟩, ⟨⟨1⟩, ⟨4⟩⟩, ⟨⟨4⟩, ⟨4⟩⟩,
    ⟨⟨5⟩, ⟨5⟩⟩, ⟨⟨6⟩, ⟨6⟩⟩, ⟨⟨7⟩, ⟨7⟩⟩].all fun key =>
  decide (roundTrip nativeSignature nativeSpell 0 (.service key) = .ok (.service key))
#guard readKey nativeSignature (.call (.generic (.ident "Context.Service") [.name ["boolean"] []])
  [.str "k4_4"]) = .error (.shape "service key")
#guard readKey nativeSignature (.call (.generic (.ident "Context.Service") [.name ["number"] []])
  [.str "k04_4"]) = .error (.shape "service key")
#guard readKey nativeSignature (.call (.ident "Context.Service") [.str "k4_4"]) =
  .error (.shape "service key")
#guard (printKey nativeSignature ⟨⟨12345678901234567890⟩, ⟨4⟩⟩).map (readKey nativeSignature) =
  .ok (.ok ⟨⟨12345678901234567890⟩, ⟨4⟩⟩)

-- The inner target is captured before the enclosing target; restoration must
-- rebuild the enclosing layer before putting the inner target back.
def nestedSharing : NativeEff :=
  .bind
    (.provideLayer
      (.merge (.succeed ⟨⟨4⟩, ⟨4⟩⟩ (.nat 7)) (.ref [0, 0, 0]))
      false (.succeed (.lit .unit)))
    (.provideLayer (.ref [0, 0]) false (.succeed (.lit .unit)))

#guard nestedSharing.layerRefsWF
#guard Effect4.Api.readable nestedSharing
#guard (Effect4.Api.typeOf nestedSharing).isSome
#guard match nestedSharing.hoistAll with
  | .ok (main, declarations) =>
    declarations.map Prod.fst == [[0, 0], [0, 0, 0]] &&
      main.restoreAll declarations == some nestedSharing
  | .error _ => false
#guard (Effect4.Api.printModule "main" nestedSharing).map Effect4.Api.readModule =
  some (.ok nestedSharing)

-- Reordering declarations is justified only when their target paths are unique.
-- With duplicate paths, restoration deliberately reads the first matching entry.
#guard
  let root : NativeEff := .provideLayer (.ref [0]) false (.succeed (.lit .unit))
  let first : LayerTerm NativeOp := .succeed ⟨⟨4⟩, ⟨4⟩⟩ (.nat 1)
  let second : LayerTerm NativeOp := .succeed ⟨⟨4⟩, ⟨4⟩⟩ (.nat 2)
  root.restoreAll [([0], first), ([0], second)] !=
    root.restoreAll [([0], second), ([0], first)]

#print axioms nativeServiceTy_profile
#print axioms Effect4.Program.Eff.hoistAll_exists
#print axioms Effect4.Program.readModule_printModule
#print axioms Effect4.Program.readable_hoistAll
#print axioms Effect4.Program.readable_layerAt
#print axioms Effect4.Program.readable_replaceLayerAt
#print axioms Effect4.Program.printModule_readable
#print axioms Effect4.Program.printModule_shape
#print axioms Effect4.Program.readModule_printModule_readable
#print axioms Effect4.Program.checkTypedProgram
#print axioms Effect4.Program.checkTypedProgram_type
#print axioms Effect4.Program.checkTypedProgram_refusal_iff
#print axioms Effect4.Program.TypedProgram.hasTy
#print axioms Effect4.Codegen.emitModule
#print axioms Effect4.Codegen.emitModule_erasure
#print axioms Effect4.Codegen.emitModule_complete
#print axioms Effect4.Codegen.ModuleEmission.readModule
#print axioms Effect4.Codegen.ModuleEmission.unique
#print axioms Effect4.Api.printDecl_erasure
#print axioms Effect4.Api.printModule_roundTrip
#print axioms Effect4.Codegen.envelopeCheck_iff
#print axioms Effect4.Codegen.layersPlain_iff
#print axioms Effect4.Codegen.mainConst_eq_some
#print axioms Effect4.Codegen.ModuleReading.recheck
#print axioms Effect4.Codegen.ModuleReading.unique
#print axioms Effect4.Codegen.ModuleReading.typing_eq
#print axioms Effect4.Codegen.admitModule_module
#print axioms Effect4.Codegen.admitModule_typed
#print axioms Effect4.Codegen.admitModule_read
#print axioms Effect4.Codegen.admitModule_bound
#print axioms Effect4.Codegen.admitModule_envelope
#print axioms Effect4.Codegen.admitModule_complete
#print axioms Effect4.Codegen.ModuleEmission.admit
#print axioms Effect4.Api.admitModule_typed
#print axioms Effect4.Api.admitModule_emitModule
#print axioms Effect4.Program.Eff.restoreAll_hoistAll
#print axioms Effect4.Program.readKey_printKey
#print axioms Effect4.Program.readKey_exact
#print axioms Effect4.Program.read_print_layer
#print axioms Effect4.Program.read_print
#print axioms Effect4.Program.read_exact
#print axioms Effect4.Program.roundTrip_eq
#print axioms Effect4.Program.roundTrip_weaken

end Test.Codegen.ReadContract
