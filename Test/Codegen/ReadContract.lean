import Effect4.Codegen.Read
import Effect4.Api
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

open Effect4.Program

/-- The four rows: a call row on a handle request, a value row, an async row, and a
read-modify-write row whose pure function trails the request. -/
def rowOf : Fin 4 → Row
  | 0 => ⟨"get", "Ref.get", .call, [], .sync, .handle "Ref.Ref<number>", .nat, .never, [],
           "Ref.ts:200"⟩
  | 1 => ⟨"count", "cell.count", .value, [], .sync, .unit, .nat, .never, [], "Ref.ts:210"⟩
  | 2 => ⟨"await", "Deferred.await", .call, [], .async,
           .handle "Deferred.Deferred<number, never>", .nat, .never, [], "Deferred.ts:120"⟩
  | 3 => ⟨"update", "Ref.update", .call, ["incr"], .sync, .handle "Ref.Ref<number>", .unit,
           .never, [], "Ref.ts:1273-1276"⟩

def sig : Signature (Fin 4) :=
  { rowOf := rowOf
  , atomOf := fun atom args => if atom = "succ" ∧ args = [Ty.nat] then some Ty.nat else none
  , scopeKey := ⟨⟨0⟩, ⟨0⟩⟩ }

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

def tupleRowOf : Bool → Row
  | false => ⟨"tuple", "Fixture.tuple", .tupleCall, [], .sync,
      .prod .nat .nat, .nat, .never, [], "§14 tuple-call fixture"⟩
  | true => ⟨"tupleAsync", "Fixture.tuple", .tupleCall, ["first", "second"], .async,
      .prod .nat .nat, .nat, .never, [], "§14 tuple-call fixture with trailing names"⟩

def tupleSig : Signature Bool :=
  { rowOf := tupleRowOf, atomOf := fun _ _ => none, scopeKey := ⟨⟨0⟩, ⟨0⟩⟩ }

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

#guard roundTrip tupleSig tupleSpell 1 (.callback true (.var 0)) =
  .ok (.callback true (.var 0))

#guard roundTrip tupleSig tupleSpell 0
    (.perform false (.app "pair" (.cons (.lit (.nat 2)) (.cons (.lit (.nat 7)) .nil)))) =
  .ok (.perform false (.app "pair" (.cons (.lit (.nat 2)) (.cons (.lit (.nat 7)) .nil))))

#guard roundTrip tupleSig tupleSpell 1
    (.callback true (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 7)) .nil)))) =
  .ok (.callback true (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 7)) .nil))))

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
  .ok (.callback true (.var 0))

-- Components of two different identifiers are an ordinary pair.
#guard readEff tupleSig tupleSpell 2 (.call (.ident "Fixture.tuple")
    [.call (.ident "fst") [.ident "a0"], .call (.ident "snd") [.ident "a1"]]) =
  .ok (.perform false (.app "pair" (.cons (.app "fst" (.cons (.var 0) .nil))
    (.cons (.app "snd" (.cons (.var 1) .nil)) .nil))))

#guard readEff tupleSig tupleSpell 1 (.call (.ident "Fixture.tuple") [.ident "a0", .int 7]) =
  .ok (.perform false (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 7)) .nil))))

-- Trailing names are matched exactly and in order: a misordered suffix is no row, so the
-- call is read as an atom application and refused on its first non-term.
#guard readEff tupleSig tupleSpell 1 (.call (.ident "Fixture.tuple")
    [.ident "a0", .int 7, .ident "second", .ident "first"]) =
  .error (.unknownIdent "second")

-- The former one-request call, a one-argument call with trailing names, and three
-- plain arguments are not tuple readings.
#guard readEff tupleSig tupleSpell 1 (.call (.ident "Fixture.tuple") [.ident "a0"]) =
  .error (.arity "Fixture.tuple")

#guard readEff tupleSig tupleSpell 1 (.call (.ident "Fixture.tuple")
    [.ident "a0", .ident "first", .ident "second"]) = .error (.arity "Fixture.tuple")

#guard readEff tupleSig tupleSpell 1 (.call (.ident "Fixture.tuple") [.ident "a0", .int 7, .int 8]) =
  .ok (.yieldError (.app "Fixture.tuple"
    (.cons (.var 0) (.cons (.lit (.nat 7)) (.cons (.lit (.nat 8)) .nil)))))

-- A call row does not accept the tuple reading.
#guard readEff sig spell 1 (.call (.ident "Ref.get") [.ident "a0", .int 1]) =
  .error (.arity "Ref.get")

-- The former wrapper is an unknown atom whose first argument is no term.
#guard readEff tupleSig tupleSpell 1 (.call (.ident "Reflect.apply")
    [.ident "Fixture.tuple", .ident "undefined", .ident "a0"]) =
  .error (.unknownIdent "Fixture.tuple")

#guard readEff tupleSig tupleSpell 0 (.ident "Reflect.apply") =
  .error (.unknownIdent "Reflect.apply")

#guard readable tupleSig tupleSpell 0 (.yieldError (.app "Reflect.apply" .nil)) = true

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

#guard roundTrip sig spell 1 (.yieldError (.var 0)) = .ok (.yieldError (.var 0))

#guard roundTrip sig spell 0 (.yieldError (.lit .unit))
  = .ok (.yieldError (.lit .unit))

#guard roundTrip sig spell 0 (.yieldError (.lit (.nat 3)))
  = .ok (.yieldError (.lit (.nat 3)))

#guard roundTrip sig spell 1 (.yieldError (.app "succ" (.cons (.var 0) .nil)))
  = .ok (.yieldError (.app "succ" (.cons (.var 0) .nil)))

#guard roundTrip sig spell 1 (.sync (.app "succ" (.cons (.var 0) .nil)))
  = .ok (.sync (.app "succ" (.cons (.var 0) .nil)))

#guard roundTrip sig spell 0 (.suspend (.succeed (.lit .unit)))
  = .ok (.suspend (.succeed (.lit .unit)))

#guard roundTrip sig spell 1 (.perform 0 (.var 0)) = .ok (.perform 0 (.var 0))

#guard roundTrip sig spell 0 (.perform 1 (.lit .unit))
  = .ok (.perform 1 (.lit .unit))

#guard roundTrip sig spell 1 (.perform 3 (.var 0)) = .ok (.perform 3 (.var 0))

#guard roundTrip sig spell 1 (.callback 2 (.var 0)) = .ok (.callback 2 (.var 0))

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

#guard roundTrip sig spell 0 (.branch (.lit (.bool true)) (.succeed (.lit (.nat 1)))
      (.succeed (.lit .unit)))
  = .ok (.branch (.lit (.bool true)) (.succeed (.lit (.nat 1))) (.succeed (.lit .unit)))

#guard roundTrip sig spell 0 (.whileLoop (.lit (.nat 0)) (.var 0) (.app "succ" (.cons (.var 1) .nil))
      (.succeed (.var 0)))
  = .ok (.whileLoop (.lit (.nat 0)) (.var 0) (.app "succ" (.cons (.var 1) .nil)) (.succeed (.var 0)))

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

#guard roundTrip sig spell 1 (.withFiber (.forkIn (.succeed (.lit (.nat 1))) ⟨true, false, .inherit⟩ (.var 0)))
  = .ok (.withFiber (.forkIn (.succeed (.lit (.nat 1))) ⟨true, false, .inherit⟩ (.var 0)))

#guard roundTrip sig spell 0 (.withFiber (.forkScoped (.succeed (.lit (.nat 1))) ⟨true, false, .interruptible⟩))
  = .ok (.withFiber (.forkScoped (.succeed (.lit (.nat 1))) ⟨true, false, .interruptible⟩))

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

#guard readable sig spell 0 (.yieldError (.app "Effect.withFiber" .nil)) = false

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

#guard readEff sig spell 0 (.call (.ident "Effect.gen") [.generator [.letDefinite "x" "number"]])
  = .error .unsupportedStmt

/-! ## What the printer loses

A `daemon` flag on a scoped fork has no field in the options object; a `perform` on an
`.async` row and a `callback` on a `.sync` row print like the row's declared kind; the request
of a `unit`-request row or a value row is dropped. Each is `readable = false`, and the reader
answers the program the printer kept. -/

#guard readable sig spell 0 (.withFiber (.forkScoped (.succeed (.lit (.nat 1))) ⟨true, true, .inherit⟩))
  = false

#guard roundTrip sig spell 0 (.withFiber (.forkScoped (.succeed (.lit (.nat 1))) ⟨true, true, .inherit⟩))
  = .ok (.withFiber (.forkScoped (.succeed (.lit (.nat 1))) ⟨true, false, .inherit⟩))

#guard readable sig spell 1 (.callback 0 (.var 0)) = false

#guard roundTrip sig spell 1 (.callback 0 (.var 0)) = .ok (.perform 0 (.var 0))

#guard readable sig spell 0 (.perform 1 (.lit (.nat 5))) = false

#guard roundTrip sig spell 0 (.perform 1 (.lit (.nat 5))) = .ok (.perform 1 (.lit .unit))

#guard readable sig spell 0 (.yieldError (.var 3)) = false

/-! ## The native profile through `Api`: trailing names and the two `Scope.make` rows -/

open Effect4.Api in
#guard roundTrip (.bind (.perform .refMake (.lit (.nat 0))) (.perform (.refUpdate .double) (.var 0)))
  = .ok (.bind (.perform .refMake (.lit (.nat 0))) (.perform (.refUpdate .double) (.var 0)))

open Effect4.Api in
#guard roundTrip (.bind (.perform (.scopeMake .parallel) (.lit .unit))
    (.perform (.scopeMake .sequential) (.lit .unit)))
  = .ok (.bind (.perform (.scopeMake .parallel) (.lit .unit)) (.perform (.scopeMake .sequential) (.lit .unit)))

open Effect4.Api in
#guard roundTrip (.bind (.perform .deferredMake (.lit .unit)) (.callback .deferredAwait (.var 0)))
  = .ok (.bind (.perform .deferredMake (.lit .unit)) (.callback .deferredAwait (.var 0)))

/-! ## The corpus: every program the generator writes, through `Api.print` and `Api.read`

`Test/Program/Gen.lean` is the seeded generator of the image-parser spike
(`docs/research/2026-09-05-image-parser-spike.md`): 400 programs at depth 4 over every
constructor the printer accepts. Four pins: how many are `readable` (the generator draws a
request for every row, so a `unit`-request row loses it; a scoped fork with `daemon` loses
that); every readable one comes back as itself (`read_print`, executed); every one of the 400
comes back as a program that prints the same tree (`read_exact`, executed); and no unreadable
one comes back unchanged, so on this corpus `readable` is exact, not merely sufficient. -/

#guard (Test.Program.Gen.corpus 400 4).length = 400

-- 324 before source-repairs §18; the fourteen generated programs whose tuple-row request
-- is neither a `pair` application nor a single-identifier term left the readable image
-- with the direct argument-list shape (`requestReadable`), and still print the same tree.
#guard ((Test.Program.Gen.corpus 400 4).filter Effect4.Api.readable).length = 310

#guard (Test.Program.Gen.corpus 400 4).all fun p =>
  !Effect4.Api.readable p || decide (Effect4.Api.roundTrip p = .ok p)

#guard (Test.Program.Gen.corpus 400 4).all fun p =>
  match Effect4.Api.roundTrip p with
  | .ok q => (Effect4.Api.print q).toOption == (Effect4.Api.print p).toOption
  | .error _ => false

#guard ((Test.Program.Gen.corpus 400 4).filter fun p =>
  !Effect4.Api.readable p && decide (Effect4.Api.roundTrip p = .ok p)).length = 0

end Test.Codegen.ReadContract
