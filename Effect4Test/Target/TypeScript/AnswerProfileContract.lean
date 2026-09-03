/-
Contract packet: `test/contracts/answer-profile.contract.md` (light ceremony).
The frozen answer-type profile: which type spellings `effect_signature` and
`effect_atoms` admit, what TypeScript they render to, what the Lean renderer
puts on the wire for each, and which spelling is refused with which reason.

Doc comments cannot precede `effect_signature`, `effect_atoms` or `#guard`, so
the receipts carry line comments; `#guard_msgs` is the one place a doc comment
appears, and it carries the expected refusal, not prose.

counterexample: E4-TARGET-CE-022 E4-TARGET-CE-023
-/

import Effect4.Meta.Derive
import Effect4.Target.TypeScript.Trace

namespace Effect4Test.Target.TypeScript.AnswerProfileContract

open Effects Effect4.Meta Effect4.Target.EffectV4
open Effects.Trace (Val ToVal)

#check @Effect4.Target.EffectV4.Spelling
#check (@Effect4.Target.EffectV4.Spelling.render : Spelling → String)
#check (@Effect4.Target.EffectV4.Spelling.depth : Spelling → Nat)
#check (@Effect4.Target.EffectV4.Spelling.admitted : Spelling → Bool)
#check (@Effect4.Target.EffectV4.Spelling.wireDefault : Spelling → Val)
#check (@Effect4.Target.EffectV4.bindingName : String → Bool)
#check @Effect4.Target.EffectV4.AtomRow
#check (@Effect4.Target.EffectV4.atomsModule : List AtomRow → String)

/-! ## Depth one and two: the spellings this packet inherits -/

#guard Spelling.nat.render = "number"
#guard Spelling.int.render = "number"
#guard Spelling.string.render = "string"
#guard Spelling.bool.render = "boolean"
#guard Spelling.unit.render = "void"
#guard (Spelling.handle "Scope.Closeable").render = "Scope.Closeable"
#guard (Spelling.option .nat).render = "Option.Option<number>"
#guard (Spelling.list .nat).render = "ReadonlyArray<number>"
#guard (Spelling.except .string .nat).render = "Result.Result<number, string>"
#guard (Spelling.prod .nat .string).render = "readonly [number, string]"
#guard Spelling.nat.depth = 1
#guard (Spelling.handle "Fiber.Fiber<number, number>").depth = 1
#guard (Spelling.except .string .nat).depth = 2

/-! ## Depth three: the five spellings this packet admits -/

#guard (Spelling.option (.except .string .nat)).render =
  "Option.Option<Result.Result<number, string>>"
#guard (Spelling.except .string (.option .nat)).render =
  "Result.Result<Option.Option<number>, string>"
#guard (Spelling.list (.prod .nat .string)).render =
  "ReadonlyArray<readonly [number, string]>"
#guard (Spelling.option (.prod .nat .string)).render =
  "Option.Option<readonly [number, string]>"
#guard (Spelling.prod .nat (.except .string .bool)).render =
  "readonly [number, Result.Result<boolean, string>]"

#guard (Spelling.option (.except .string .nat)).depth = 3
#guard (Spelling.except .string (.option .nat)).depth = 3
#guard (Spelling.list (.prod .nat .string)).depth = 3
#guard (Spelling.option (.prod .nat .string)).depth = 3
#guard (Spelling.prod .nat (.except .string .bool)).depth = 3
#guard (Spelling.option (.except .string .nat)).admitted
#guard (Spelling.list (.prod .nat .string)).admitted

-- Depth four is outside the profile, whichever constructor nests it.
#guard (Spelling.option (.option (.except .string .nat))).depth = 4
#guard !(Spelling.option (.option (.except .string .nat))).admitted
#guard !(Spelling.list (.prod .nat (.option (.list .nat)))).admitted
#guard Spelling.profileDepth = 3

/-! ## The same five spellings through `effect_signature`

`tsOfType` is the elaborator's private parser; these rows are its image. -/

effect_signature Depth3 where
  | optExcept (k : Nat) : Option (Except String Nat) ⟪ "an optional result" ⟫
  | exceptOpt (k : Nat) : Except String (Option Nat) ⟪ "a result of an option" ⟫
  | listPair (k : Nat) : List (Nat × String) ⟪ "a list of pairs" ⟫
  | optPair (k : Nat) : Option (Nat × String) ⟪ "an optional pair" ⟫
  | pairExcept (k : Nat) : Nat × Except String Bool ⟪ "a pair with a result" ⟫

#guard Depth3.rows.ops.map (·.tsAnswer) =
  [ "Option.Option<Result.Result<number, string>>"
  , "Result.Result<Option.Option<number>, string>"
  , "ReadonlyArray<readonly [number, string]>"
  , "Option.Option<readonly [number, string]>"
  , "readonly [number, Result.Result<boolean, string>]" ]

-- Both `effect` namespaces are needed once a spelling nests them, so the
-- generated module imports both. A prefix test would have missed `Result`.
#guard Depth3.rows.namespaces = ["Option", "Result"]
#guard Depth3.rows.usesResult

-- The module's own import subtracts what a supplied import already binds, so a
-- caller that imports `Option` as a type-only binding gets no duplicate.
#guard neededNamespaces Depth3.rows.spellings [] = ["Option", "Result"]
#guard neededNamespaces Depth3.rows.spellings [.types ["Option"] "effect"] = ["Result"]

-- A parameter is spelled by the same profile as an answer.
effect_signature Depth3Param where
  | store (r : Option (Except String Nat)) : Unit ⟪ "store an optional result" ⟫

#guard Depth3Param.rows.ops.map (fun row => row.tsParams.map (·.2)) =
  [["Option.Option<Result.Result<number, string>>"]]

-- Every depth-three answer is `Inhabited`, which is what `X.answerDefault`
-- (the per-program receipt of `effect_program`) needs; and its default is the
-- wire inhabitant of its spelling.
#guard Depth3.encodeAnswer .optExcept (Depth3.answerDefault .optExcept) =
  (Spelling.option (.except .string .nat)).wireDefault
#guard Depth3.encodeAnswer .listPair (Depth3.answerDefault .listPair) =
  (Spelling.list (.prod .nat .string)).wireDefault
#guard Depth3.encodeAnswer .pairExcept (Depth3.answerDefault .pairExcept) =
  (Spelling.prod .nat (.except .string .bool)).wireDefault

/-! ## The refused spelling, with its reason -/

/--
error: effect_signature: the answer-type profile admits depth 3 at most; this spelling has depth 4
-/
#guard_msgs in
effect_signature Depth4 where
  | tooDeep (k : Nat) : Option (Option (Except String Nat)) ⟪ "one nesting too many" ⟫

/--
error: effect_signature: no TypeScript spelling for `Float`; add a Stratum V row first
-/
#guard_msgs in
effect_signature Foreign where
  | notInProfile (k : Nat) : Float ⟪ "not a profile type" ⟫

/-! ## The wire: the Lean renderer on each depth-three answer

These are the exact bytes a golden carries and the host must reproduce; the
host's decoder is `wireAnswer` in `harness/trace/tracer.ts`, a case analysis
over the same grammar. -/

open Effect4.Target.TypeScript.Trace in
#guard val (ToVal.toVal (Option.some (Except.ok 7) : Option (Except String Nat))) =
  "{\"some\":[true, 7]}"

open Effect4.Target.TypeScript.Trace in
#guard val (ToVal.toVal (Option.some (Except.error "boom") : Option (Except String Nat))) =
  "{\"some\":[false, \"boom\"]}"

open Effect4.Target.TypeScript.Trace in
#guard val (ToVal.toVal (Option.none : Option (Except String Nat))) = "{\"none\":true}"

open Effect4.Target.TypeScript.Trace in
#guard val (ToVal.toVal (Except.ok (Option.some 7) : Except String (Option Nat))) =
  "[true, {\"some\":7}]"

open Effect4.Target.TypeScript.Trace in
#guard val (ToVal.toVal ([(1, "a"), (2, "b")] : List (Nat × String))) =
  "[[1, \"a\"], [[2, \"b\"], []]]"

open Effect4.Target.TypeScript.Trace in
#guard val (ToVal.toVal (Option.some (1, "a") : Option (Nat × String))) =
  "{\"some\":[1, \"a\"]}"

open Effect4.Target.TypeScript.Trace in
#guard val (ToVal.toVal ((1, Except.ok true) : Nat × Except String Bool)) =
  "[1, [true, true]]"

-- The corpus row: the answer of `Tri.lookup` in `generated/traces/probe.empty.tsv`.
open Effect4.Target.TypeScript.Trace in
#guard rows [.answer "lookup" (ToVal.toVal (Option.some (Except.ok 44) : Option (Except String Nat)))] =
  "answer\tlookup\t{\"some\":[true, 44]}\n"

/-! ## `wireDefault`: the inhabitant of each spelling

`ToVal` of the Lean inhabitant of the type is exactly `wireDefault` of its
spelling, so a face with nothing to answer answers the same bytes on both
sides. -/

#guard (Spelling.option (.except .string .nat)).wireDefault =
  ToVal.toVal (Option.none : Option (Except String Nat))
-- Lean's `Inhabited (Except ε α)` is the error side, so the wire inhabitant of
-- a `Result` spelling is `[false, …]`, not `[true, …]`.
#guard (Spelling.except .string (.option .nat)).wireDefault =
  ToVal.toVal (Except.error "" : Except String (Option Nat))
#guard (Spelling.except .string (.option .nat)).wireDefault = .pair (.bool false) (.str "")
#guard (Spelling.list (.prod .nat .string)).wireDefault =
  ToVal.toVal ([] : List (Nat × String))
#guard (Spelling.prod .nat (.except .string .bool)).wireDefault =
  ToVal.toVal ((0, Except.error "") : Nat × Except String Bool)
#guard Spelling.unit.wireDefault = ToVal.toVal ()
#guard Spelling.nat.wireDefault = ToVal.toVal (0 : Nat)
#guard (Spelling.handle "Scope.Closeable").wireDefault =
  ToVal.toVal (default : Handle "Scope.Closeable")

/-! ## `OfVal`: the decoding side, the exact inverse of `ToVal` -/

-- `Except` carries no `DecidableEq`, so the round trip is compared on the wire.
#guard ((OfVal.ofVal (ToVal.toVal (Option.some (Except.ok 7) : Option (Except String Nat)))
    : Option (Option (Except String Nat))).map ToVal.toVal) =
  Option.some (ToVal.toVal (Option.some (Except.ok 7) : Option (Except String Nat)))
#guard (OfVal.ofVal (ToVal.toVal ([(1, "a")] : List (Nat × String)))
  : Option (List (Nat × String))) = Option.some [(1, "a")]
#guard (OfVal.ofVal (Val.str "x") : Option Nat) = Option.none

/-! ## The binding profile

`TypeScript.reservedIdentifiers` (lean4-typescript v0.4.2) carries the
ECMAScript reserved words; `reservedExtra` adds the predefined names it does
not, and `bindingName` is the conjunction the DSL checks. -/

#guard !bindingName "delete"
#guard !bindingName "await"
#guard !bindingName "yield"
#guard !bindingName "arguments"
#guard !bindingName "eval"
#guard !bindingName "undefined"
#guard !bindingName "NaN"
#guard bindingName "lookup"
#guard bindingName "succ"

/--
error: effect_signature: `await` is not a legal target identifier
-/
#guard_msgs in
effect_signature Reserved where
  | await (k : Nat) : Unit ⟪ "a reserved binding" ⟫

/--
error: effect_signature: `arguments` is not a legal target identifier
-/
#guard_msgs in
effect_signature Predefined where
  | arguments (k : Nat) : Unit ⟪ "a predefined name" ⟫

/-! ## `effect_atoms`: one declaration, every face -/

effect_atoms ProfileAtoms where
  | bump (n : Nat) : Nat ⟪ "n + 1" ⟫ := n + 1
  | firstOr (r : Option (Except String Nat)) : Nat
      ⟪ "Option.isSome(r) ? (Result.isSuccess(r.value) ? r.value.success : 0) : 0" ⟫ :=
      (match r with | Option.some (.ok n) => n | _ => 0)

-- The Lean face.
#guard bump 4 = 5
#guard firstOr (Option.some (Except.ok 7)) = 7
#guard firstOr Option.none = 0

-- The wire face, derived from the same row.
#guard ProfileAtoms.eval "bump" (.nat 4) = .nat 5
#guard ProfileAtoms.eval "firstOr" (.some (.pair (.bool true) (.nat 7))) = .nat 7
#guard ProfileAtoms.eval "firstOr" .none = .nat 0
#guard ProfileAtoms.eval "notAnAtom" (.nat 4) = .unit

-- The flow-embedding face.
#guard ProfileAtoms.table =
  [ ("bump", "number", "number")
  , ("firstOr", "Option.Option<Result.Result<number, string>>", "number") ]

-- The TypeScript face: the row's binder, both spellings, and the host body.
#guard ProfileAtoms.rows.map (·.name) = ["bump", "firstOr"]
#guard ProfileAtoms.rows.map (·.binder) = ["n", "r"]
#guard ProfileAtoms.rows.map (·.request) = ["Nat", "Option (Except String Nat)"]
#guard (ProfileAtoms.rows.map AtomRow.constSource).head! =
  "/** Host body of the pure atom `bump`; its Lean model is `bump`. */\nexport const bump = (n: number): number => n + 1\n"

-- A depth-three atom pulls both `effect` namespaces into the generated module.
#guard Spelling.namespacesOf (ProfileAtoms.rows.map (·.tsRequest)) = ["Option", "Result"]
#guard ProfileAtoms.source = atomsModule ProfileAtoms.rows

/--
error: effect_atoms: `eval` is not a legal target identifier
-/
#guard_msgs in
effect_atoms ReservedAtoms where
  | eval (n : Nat) : Nat ⟪ "n" ⟫ := n

end Effect4Test.Target.TypeScript.AnswerProfileContract
