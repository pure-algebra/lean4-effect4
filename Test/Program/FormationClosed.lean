import Effect4.Laws.Program.Typing.Closed
import Effect4.Laws.Codegen.Checked
import Effect4.Api
import Test.Program.Gen

/-!
# Formation at a type variable, and the checker's closed types

Finite controls of the clause "a type variable is formed in a template only"
(`Formation.HeadFormed`, decisions row 288, point 6 a) and of `check_closed`
(`src/Effect4/Laws/Program/Typing/Closed.lean`, the claim `checked-types-closed`).

- **Red.** Each kind of annotation site refuses a variable, with the reason `typeVariable` and
  the variable's path: a record's declaration, an operation's type argument, a loop's cursor
  type, a list fold's stated accumulator, and an operation's binder term. Every checked
  boundary shares the refusal.
- **Green.** A row whose columns hold a parameter is still formed, in a table and at each use.
  Each native row is formed as a template. A closed annotation is formed at each site.
- **The theorem's premises.** Each premise of `check_closed` has a program that shows it is
  needed: without it the checker answers a type that is not closed.
- **A declared carrier.** A service carrier is a strict formation site, so admission refuses a
  signature whose carrier holds a variable, and an admitted program has closed types.
- **A count.** No program of the generated corpus and of the wire corpus holds a variable in
  an annotation.

Each `#guard` is a finite check. They establish no host behaviour.
-/

namespace Test.Program.FormationClosed

open Effect4 Effect4.Program

/-! ## The programs -/

/-- A type that is not closed: `number | T2`. -/
def openTy : Ty := .union .nat (.var 2)

/-- `succeed` of the empty record whose optional field `a` is declared at `T7`. -/
def recordOpen : NativeEff := .succeed (.record [("a", true, .var 7)] [] .nil)

/-- `Deferred.make<T5, number>()`. -/
def typeArgOpen : NativeEff := .perform (.deferredMakeOf (.var 5) .nat) (.lit .unit)

/-- A loop whose cursor type is stated at `number | T2`. -/
def cursorOpen : NativeEff :=
  .iterate (some openTy) (.lit (.nat 0)) (.lit (.bool false)) (.var 0) (.var 0)
    (.succeed (.lit .unit))

/-- A list fold whose accumulator is stated at `number | T2`. -/
def accumulatorOpen : NativeEff :=
  .succeed (.fold (some openTy) (.app "nil" .nil) (.lit (.nat 0)) (.var 0))

/-- `Ref.make(0)`, then `Ref.update` whose binder term holds the same fold. -/
def binderOpen : NativeEff :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.perform (.refUpdateWith (.fold (some openTy) (.app "nil" .nil) (.var 1) (.var 2)))
      (.var 0))

/-- The five programs, one per kind of annotation site. -/
def open5 : List NativeEff := [recordOpen, typeArgOpen, cursorOpen, accumulatorOpen, binderOpen]

/-- The same five sites at closed types. -/
def closed5 : List NativeEff :=
  [ .succeed (.record [("a", true, .nat)] [] .nil)
  , .perform (.deferredMakeOf .unit .never) (.lit .unit)
  , .iterate (some (.union .nat .string)) (.lit (.nat 0)) (.lit (.bool false)) (.var 0)
      (.var 0) (.succeed (.lit .unit))
  , .succeed (.fold (some (.list .nat)) (.app "nil" .nil) (.app "nil" .nil) (.var 0))
  , .bind (.perform .refMake (.lit (.nat 0)))
      (.perform (.refUpdateWith (.fold (some .nat) (.app "nil" .nil) (.var 1) (.var 2)))
        (.var 0)) ]

/-! ## Red: a variable in an annotation is refused at formation -/

/-- The first refusal of raw formation of a program with no row table. -/
def refusal (e : NativeEff) : Option (List String × Ty × FormationReason) :=
  (Formation.checkInput e []).map fun (why : FormationRefusal) => (why.path, why.ty, why.reason)

#guard refusal recordOpen =
  some (["program", "argument", "0", "term", "fields", "type", "1"], .var 7, .typeVariable)
#guard refusal typeArgOpen =
  some (["program", "argument", "0", "op", "typeArgs", "0", "type", "0"], .var 5,
    .typeVariable)
#guard refusal cursorOpen = some (["program", "cursorTy", "type", "2"], .var 2, .typeVariable)
#guard refusal accumulatorOpen =
  some (["program", "argument", "0", "term", "accTy", "type", "2"], .var 2, .typeVariable)
#guard (refusal binderOpen).map (·.2) = some (.var 2, .typeVariable)
#guard (refusal binderOpen).any fun why =>
  why.1.take 6 == ["program", "1", "argument", "0", "op", "term"]

-- Every checked boundary shares the refusal: admission, the module's production, the
-- declaration and the checked replay.
#guard open5.all fun e =>
  match admitProgram e {} with
  | .error (.formation why) => why.reason == .typeVariable
  | _ => false
#guard open5.all fun e =>
  match Effect4.Api.emitModule "main" e with
  | .error (.formation why) => why.reason == .typeVariable
  | _ => false
#guard open5.all fun e => (Effect4.Api.printDecl "main" e).isNone
#guard open5.all fun e =>
  match Effect4.Api.replayChecked e 10 [] with
  | .inr (.formation why) => why.reason == .typeVariable
  | _ => false

/-! ### The checker's two rules that read strict formation

The term typer checks a record's declaration, and the row rule checks each instantiated column.
So the checker refuses these two by itself, with no formation pass before it. -/

#guard Effect4.Api.typeOf recordOpen = none
#guard match Effect4.Api.explain recordOpen with
  | some ⟨[], .recordTerm ⟨_, .declarationFormation why⟩⟩ =>
    why.ty == .var 7 && why.reason == .typeVariable
  | _ => false

/-- A host row for the controls. -/
def host (request answer : Ty) : Row :=
  { name := "query", spelling := "Host.query", kind := .async, registration := .external,
    request, answer, cite := "formation closed" }

/-- A row template: its request binds the parameter that its answer names. -/
def templateRow : Row := host (.var 0) (.list (.var 0))

-- A request whose type holds a variable binds the row's parameter to it, and the instantiated
-- column is refused. Until the clause, formation had no rule at a variable.
#guard match checkRow templateRow (.var 3) with
  | .error (.formation why) =>
    why.path == ["row", "request", "type", "0"] && why.ty == .var 3 &&
      why.reason == .typeVariable
  | _ => false

/-! ## Green: a template may hold a parameter -/

-- The head judgment: formed in a template, refused outside one.
example : Formation.HeadFormed true (.var 3) := rfl
example : ¬ Formation.HeadFormed false (.var 3) := Bool.noConfusion

-- A supplied row whose columns hold a parameter is formed in its table, typed at each use, and
-- admitted with a program that performs it.
#guard Formation.checkInput (.succeed (.lit (.nat 1)) : NativeEff) [templateRow] = none
#guard rowTy templateRow .nat = some (.pure (.list .nat))
#guard (admitProgram (.perform (.external 0) (.lit (.nat 1))) ⟨[templateRow], []⟩).isOk
#guard (Effect4.Api.typeOf (.perform (.external 0) (.lit (.nat 1))) [templateRow]).map (·.answer)
  = some (.list .nat)

-- Each native row is formed as a template: the `Ref` and `Deferred` rows hold parameters. The
-- same column is refused where no template is expected.
#guard Formation.check (Formation.tableSites (NativeOp.spelled.map NativeOp.row)) = none
#guard (Formation.check (Formation.sites false [] (NativeOp.row .refGet).request)).map (·.reason) =
  some .typeVariable

-- A program that uses the template rows is admitted: the checker instantiates each parameter.
#guard (admitProgram (.bind (.perform .refMake (.lit (.nat 0))) (.perform .refGet (.var 0)))
  {}).isOk

-- A closed annotation is formed at each of the five sites, and the checker's types are closed.
#guard closed5.all fun e => (Formation.checkInput e []).isNone
#guard closed5.all fun e =>
  (Effect4.Api.typeOf e).any fun t => t.answer.closed && t.error.closed

/-! ## `check_closed`, and what each premise is for -/

/-- `check_closed` at the native signature of any row table: a formed program that the checker
admits has closed types, with no premise on the signature. -/
example (table : RowTable) {e : NativeEff} {t : EffTy}
    (formed : Formation.Formed (Formation.programSites e))
    (h : Checker.check (nativeSignature table) [] [] e = .ok t) :
    t.answer.closed = true ∧ t.error.closed = true :=
  check_closed _ (closedSig_native table) ClosedEnv.nil formed h

/-- The checker's answer alone, and whether it is closed. -/
def answer (e : NativeEff) (table : RowTable := []) : Option (Ty × Bool) :=
  (Effect4.Api.typeOf e table).map fun (t : EffTy) => (t.answer, t.answer.closed)

-- **The formation premise.** The checker alone types a stated cursor and a stated accumulator
-- at the stated type, `number | T2`. It is formation that refuses the two programs above.
#guard answer cursorOpen = some (openTy, false)
#guard answer accumulatorOpen = some (openTy, false)
#guard openTy.renderRaw = "number | T2"
-- An operation's type argument is closed to `never` by the row's instance, without a word:
-- `Deferred.make<T5, number>()` is typed at `Deferred<never, number>`.
#guard answer typeArgOpen = some (.deferredOf .never .nat, true)

-- **The environment premise.** A variable of a term has the environment's type.
#guard (effTy (nativeSignature []) [.var 0] (.succeed (.var 0))).map (·.answer.closed) =
  some false

/-- A typing signature whose one atom answers a parameter. -/
def openAtoms : Signature NativeOp := { nativeSignature [] with atomOf := fun _ _ => some (.var 0) }

-- **The atom premise.** An atom's scheme is no formation site: the program is formed, and its
-- type is the atom's answer.
#guard (Formation.checkInput (.succeed (.app "open" .nil) : NativeEff) []).isNone
#guard (typeOfProgram openAtoms (.succeed (.app "open" .nil))).map (·.answer.closed) = some false

/-- The signature of `openAtoms` has no closed atoms. -/
theorem openAtoms_not_closed : ¬ ClosedSig openAtoms := fun closed =>
  Bool.noConfusion (closed.atom "open" [] (.var 0) rfl (fun _ h => nomatch h))

/-- A free service key for the control. -/
def cellKey : ServiceKey := ⟨⟨20⟩, ⟨20⟩⟩

/-- An application's signature that declares the carrier `Ref<T3>`. -/
def openCarrier : SigApp := { services := [(cellKey, .refOf (.var 3))] }

-- **The carrier premise.** A carrier is no annotation of a program, and the signature's local
-- checks accept a cell at any type. The checker alone answers the carrier as it is declared,
-- `Ref.Ref<T3>`.
#guard admitSig openCarrier = .ok ()
#guard (Formation.checkInput (.service cellKey : NativeEff) openCarrier.rows).isNone
#guard (typeOfProgram openCarrier.signature (.service cellKey)).map
  (fun t => (t.answer, t.answer.closed)) = some (.refOf (.var 3), false)
#guard (Ty.refOf (.var 3)).renderRaw = "Ref.Ref<T3>"

/-- The signature of `openCarrier` has no closed carriers. -/
theorem openCarrier_not_closed : ¬ ClosedSig openCarrier.signature := fun closed =>
  Bool.noConfusion (closed.service cellKey (.refOf (.var 3)) (by decide +kernel))

/-! ## A declared carrier is a strict formation site

A carrier is no template: `Effect.service(key)` answers it as it is declared. So the formation
pass checks each declared carrier strictly (`Formation.serviceSites`), and admission refuses a
signature whose carrier holds a variable. Until this step `admitProgram` admitted the program
above at `Ref.Ref<T3>`. -/

#guard Formation.checkInput (.service cellKey : NativeEff) openCarrier.rows openCarrier.services =
  some ⟨["service", "0", "carrier", "type", "1"], .var 3, .typeVariable⟩
#guard match admitProgram (.service cellKey) openCarrier with
  | .error (.formation why) =>
    why.path == ["service", "0", "carrier", "type", "1"] && why.ty == .var 3 &&
      why.reason == .typeVariable
  | _ => false

/-- An application's signature that declares one carrier. -/
def declaring (carrier : Ty) : SigApp := { services := [(cellKey, carrier)] }

-- The other clauses of formation hold at a carrier too: a repeated field name, a map key that
-- is no string, and a deferred's error column outside the error alphabet. The signature's
-- local checks accept each of the three cells, and formation refuses each.
#guard [ (Ty.refOf (.record [("x", false, .nat), ("x", true, .string)]),
          FormationReason.repeatedField "x")
       , (.refOf (.map .nat .nat), .mapKey)
       , (.refOf (.deferredOf .nat .bool), .deferredError) ].all fun (carrier, reason) =>
  admitSig (declaring carrier) = .ok () &&
    match admitProgram (.succeed (.lit .unit)) (declaring carrier) with
    | .error (.formation why) => why.reason == reason
    | _ => false

-- Green: a closed, formed carrier is admitted, and a boundary with no declared carrier reads
-- the same sites as before.
#guard [Ty.refOf .nat, .string, .refOf (.record [("x", false, .nat)])].all fun carrier =>
  (admitProgram (.succeed (.lit .unit)) (declaring carrier)).isOk
#guard closed5.all fun e =>
  Formation.input e [templateRow] = Formation.tableSites [templateRow] ++ Formation.programSites e

/-- An admitted program has closed types, with no premise on its signature. -/
example {program : NativeEff} {app : SigApp} (admitted : AdmittedProgram program app) :
    admitted.ty.answer.closed = true ∧ admitted.ty.error.closed = true :=
  admitted.closed

/-! ## A layer reference: the expansion states what the program states

The whole-program checker types a program's expansion, and formation reads the stored program.
`typeOfProgram_closed` asks formation of the stored program alone. -/

/-- The service key of a number. -/
def numberKey : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩

/-- A layer whose body states a list fold's accumulator at the given type. -/
def stating (ty : Ty) : LayerTerm NativeOp :=
  .effect numberKey (.succeed (.fold (some ty) (.app "nil" .nil) (.lit (.nat 0)) (.var 0)))

/-- A program whose second layer refers to its first: the reference at `[0, 1]` names the layer
at `[0, 0]`. -/
def referring (ty : Ty) : NativeEff :=
  .provideLayer (.merge (stating ty) (.ref [0, 0])) false (.service numberKey)

-- The stored program states the type once, and its expansion states it twice.
#guard (referring .nat).layerRefsWF
#guard (Formation.programAnnotations (referring .nat)).map (·.2) = [.nat]
#guard (Formation.programAnnotations (referring .nat).expandRefs).map (·.2) = [.nat, .nat]
-- Green: the program is formed and admitted, at closed types.
#guard (admitProgram (referring .nat) {}).isOk
#guard answer (referring .nat) = some (.nat, true)
-- Red: a variable in the one stored annotation is refused, at the layer's path.
#guard refusal (referring openTy) =
  some (["program", "0", "0", "0", "argument", "0", "term", "accTy", "type", "2"], .var 2,
    .typeVariable)

/-- `typeOfProgram_closed` at a program with a layer reference: the formation premise is the
stored program's. -/
example {t : EffTy} (h : typeOfProgram (nativeSignature []) (referring .nat) = some t) :
    t.answer.closed = true ∧ t.error.closed = true :=
  typeOfProgram_closed _ (closedSig_native [])
    ((Formation.check_eq_none_iff _).mp (by decide +kernel)) h

/-! ## A count: no program of the two corpora holds a variable in an annotation -/

/-- A program that holds a type variable in an annotation. -/
def holdsVariable (e : NativeEff) : Bool :=
  (Formation.programAnnotations e).any fun annotation => !annotation.2.closed

#guard open5.all holdsVariable
#guard closed5.all fun e => !holdsVariable e
-- The generated corpus (`Test/Program/Gen.lean`, 400 programs at depth 4) and the wire corpus.
#guard Test.Program.Gen.sample.length = 400
#guard (Test.Program.Gen.sample.filter holdsVariable).length = 0
#guard (Wire.Corpus.all.filter fun entry => holdsVariable entry.2).length = 0
-- So no program of either corpus is refused with the new reason.
#guard Test.Program.Gen.sample.all fun e =>
  !(refusal e).any fun why => why.2.2 == .typeVariable

end Test.Program.FormationClosed
