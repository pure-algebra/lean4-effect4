import Effect4.Codegen.Styles
import Effect4.Program.Wire
import OCaml5.Eff.Goldens
import TypeScript.Render

/-! Rendering and corpus construction for Codegen.Styles. This IO tool is outside the
semantic audit. The library's target data has no raw-source constructor. -/

namespace Tools.Styles

open Effect4 Effect4.Program Effect4.Codegen
open Effect4.Codegen.Styles

mutual
  def render : Expr → String
    | .leaf e => TypeScript.Render.expr TypeScript.house0 0 e
    | .call f xs => render f ++ "(" ++ ", ".intercalate (renders xs) ++ ")"
    | .method x n xs => "(" ++ render x ++ ")." ++ n ++ "(" ++ ", ".intercalate (renders xs) ++ ")"
    | .member x n => "(" ++ render x ++ ")." ++ n
    | .generic f ts => render f ++ "<" ++ ", ".intercalate ts ++ ">"
    | .object fs => "({ " ++ ", ".intercalate (renderFields fs) ++ " })"
    | .arr xs => "[" ++ ", ".intercalate (renders xs) ++ "]"
    | .lambda ps e => "(" ++ ", ".intercalate ps ++ ") => " ++ render e
    | .generator ss => "function* () {\n" ++ String.join (renderStmts ss) ++ "}"
    | .arrowBlock ps ss => "(" ++ ", ".intercalate ps ++ ") => {\n" ++ String.join (renderStmts ss) ++ "}"
    | .cond t a b => "(" ++ render t ++ " ? " ++ render a ++ " : " ++ render b ++ ")"
    | .atomLambda .addOne => "(x) => x + 1"
    | .atomLambda .multiplyTwo => "(x) => x * 2"
    | .atomLambda .optionNone => "(_) => Option.none()"
    | .atomLambda .positiveThenZero => "(x) => x > 0 ? Option.some(0) : Option.none()"
  def renders : List Expr → List String
    | [] => [] | x :: xs => render x :: renders xs
  def renderFields : List (String × Expr) → List String
    | [] => [] | (name, x) :: xs => (name ++ ": " ++ render x) :: renderFields xs
  def renderStmt : Stmt → String
    | .constYield n x => "const " ++ n ++ " = yield* " ++ render x ++ ";\n"
    | .yieldDiscard x => "yield* " ++ render x ++ ";\n"
    | .ret x => "return " ++ render x ++ ";\n"
    | .ifElse t a b skipElse => "if (" ++ render t ++ ") {\n" ++ String.join (renderStmts a) ++ "}" ++
        (if skipElse then "\n" else " else {\n" ++ String.join (renderStmts b) ++ "}\n")
    | .whileTrue label body => (label.map (· ++ ": ")).getD "" ++ "while (true) {\n" ++ String.join (renderStmts body) ++ "}\n"
    | .letInit n x => "let " ++ n ++ " = " ++ render x ++ ";\n"
    | .assign n x => n ++ " = " ++ render x ++ ";\n"
    | .expr x => render x ++ ";\n"
    | .leaf s => TypeScript.Render.stmt TypeScript.house0 0 s ++ ";\n"
  def renderStmts : List Stmt → List String
    | [] => [] | x :: xs => renderStmt x :: renderStmts xs
end

structure Case where
  name : String
  style : Style := {}
  aliasMode : Nat := 0
  trivia : Nat := 0

def effectHeads : List String :=
  (reserved ++ Forms.all.map (·.head) ++ ["Effect.sleep", "Effect.currentTimeMillis"]).eraseDups.filter
    (fun h => h.startsWith "Effect.")

def aliases (mode : Nat) : List (String × String) :=
  if mode == 1 then effectHeads.map fun name => (name, "E." ++ (name.drop 7).toString)
  else if mode == 2 then effectHeads.zipIdx.map fun (name, i) => (name, "h" ++ toString i)
  else []

def imports (mode : Nat) : String :=
  "import { Effect, Ref, Deferred, Scope, Fiber, Layer, Context, Cause, Duration, Option, pipe } from \"effect\"\n" ++
  (if mode == 1 then "import * as E from \"effect/Effect\"\n"
   else if mode == 2 then "import { " ++ ", ".intercalate (effectHeads.zipIdx.map fun (name, i) =>
     (name.drop 7).toString ++ " as h" ++ toString i) ++ " } from \"effect/Effect\"\n"
   else "")

def Case.config (c : Case) : Style := { c.style with aliases := aliases c.aliasMode }

def source (c : Case) (expr : Expr) (key : Bool := false) : String :=
  let base := imports c.aliasMode ++
    (if key then "const Key = Context.Service<number>(\"k4_4\")\n" else "") ++
    "export const program = " ++ render expr ++ ";\n"
  if c.trivia == 1 then "// Generated foreign spelling; same program oracle.\n\n" ++ base.replace ";\n" "; /* trivia */\n\n"
  else if c.trivia == 2 then base.replace "\n" "\r\n"
  else base

def pipes : List PipeStyle := [.direct, .method, .function, .curried, .eta]
def durations : List DurationStyle := [.number, .text, .millis, .seconds, .minutes, .hours, .days, .weeks]

def isolated : List Case :=
  [{ name := "baseline" }] ++
  (pipes.drop 1).zipIdx.map (fun (p, i) => { name := s!"pipe{i}", style := { pipe := p } }) ++
  (durations.drop 1).zipIdx.map (fun (d, i) => { name := s!"duration{i}", style := { duration := d } }) ++
  [{ name := "lambdas", style := { lambdas := true } },
   { name := "options", style := { omitOptions := true } },
   { name := "release", style := { releaseOne := true } },
   { name := "else", style := { omitElse := true } },
   { name := "fields", style := { reverseFields := true } },
   { name := "namespace", aliasMode := 1 }, { name := "named", aliasMode := 2 },
   { name := "comments", trivia := 1 }, { name := "crlf", trivia := 2 }]

/-- Full products of the nine axes. Each runs the composite probe; each isolated axis
also runs the complete generated/handwritten corpus and every derived-form example. -/
def products : List Case := Id.run do
  let mut result := []
  let mut i := 0
  for pipe in pipes do
    for duration in durations do
      for aliasMode in [0, 1, 2] do
        for trivia in [0, 1, 2] do
          for mask in List.range 32 do
            let config : Style := {
              pipe := pipe
              duration := duration
              lambdas := mask % 2 == 1
              omitOptions := (mask / 2) % 2 == 1
              releaseOne := (mask / 4) % 2 == 1
              omitElse := (mask / 8) % 2 == 1
              reverseFields := (mask / 16) % 2 == 1
            }
            let item : Case := {
              name := s!"product{i}"
              aliasMode := aliasMode
              trivia := trivia
              style := config
            }
            result := item :: result
            i := i + 1
  return result.reverse

def composite : Eff NativeOp :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.scoped (.gen (.cons (.yieldDiscard (.perform (.refUpdate .incr) (.var 0)))
      (.cons (.yieldDiscard (.perform (.refUpdate .takeAndBump) (.var 0)))
      (.cons (.yieldDiscard (.perform .sleep (.lit (.nat 604800000))))
      (.cons (.yieldDiscard (.withFiber (.fork (.succeed (.lit .unit)) (Forms.defaults false))))
      (.cons (.yieldDiscard (.acquireRelease (.succeed (.lit (.nat 8))) (.succeed (.lit .unit))))
      (.cons (.yieldDiscard (.matchCause (.succeed (.lit (.nat 1))) (.succeed (.lit (.nat 2))) (.succeed (.lit (.nat 3)))))
      (.cons (.ifElse (.lit (.bool true)) .nil .nil)
      (.cons (.ret (.lit .unit)) .nil))))))))))

/-- Extra probes force all four permitted lambda shapes and the named retention, exact
fractional duration spelling, all tuple functions and the option/empty-else axes. -/
def probes : List (String × Eff NativeOp) :=
  [("composite", composite), ("fractionalDuration", .perform .sleep (.lit (.nat 1500)))] ++
  [Effect4.Machine.FnName.incr, .double, .zeroWhenPositive, .noChange, .takeAndBump].map
    (fun f => (NativeOp.fnSpelling f,
      .bind (.perform .refMake (.lit (.nat 2))) (.perform (.refUpdate f) (.var 0))))

def write (dir : System.FilePath) (name : String) (c : Case) (expr : Expr)
    (oracle : Eff NativeOp) (key : Bool := false) : IO String := do
  let text := source c expr key
  IO.FS.writeFile (dir / (name ++ ".ts")) text
  IO.FS.writeFile (dir / (name ++ ".json")) ((OCaml5.Eff.effV oracle).json ++ "\n")
  IO.FS.writeBinFile (dir / (name ++ ".eff")) ⟨(Wire.encodeProgram oracle).toArray⟩
  return s!"{name}\t{c.name}\t{text.utf8ByteSize}\n"

def corpus (dir : System.FilePath) (programs : List (String × Eff NativeOp)) : IO Unit := do
  IO.FS.createDirAll dir
  let mut index : Array String := #["name\tstyle\tbytes\n"]
  let mut counts : Array String := #["style\tfiles\n"]
  let mut total := 0
  for c in isolated do
    let mut count := 0
    for (name, p) in programs ++ probes do
      let .ok printed := print nativeSignature 0 p | throw (IO.userError s!"style printer refused {name}")
      let .ok oracle := roundTrip nativeSignature nativeSpell 0 p | throw (IO.userError s!"style oracle refused {name}")
      index := index.push (← write dir (c.name ++ "-" ++ name) c (expression c.config printed) oracle)
      count := count + 1
    for f in Forms.all do
      for n in [0, 1, 2, 5] do
        let some oracle := f.example n | throw (IO.userError s!"missing form example {f.id}")
        let some expr := Form.foreign f c.config n | throw (IO.userError s!"missing foreign example {f.id}")
        index := index.push (← write dir s!"{c.name}-form-{f.id}-{n}" c expr oracle (f.id == "yieldKey"))
        count := count + 1
    counts := counts.push s!"{c.name}\t{count}\n"
    total := total + count
  let .ok printed := print nativeSignature 0 composite | throw (IO.userError "composite refused")
  let .ok oracle := roundTrip nativeSignature nativeSpell 0 composite | throw (IO.userError "composite oracle refused")
  for c in products do
    index := index.push (← write dir c.name c (expression c.config printed) oracle)
    counts := counts.push s!"{c.name}\t1\n"
    total := total + 1
  IO.FS.writeFile (dir / "index.tsv") (String.join index.toList)
  IO.FS.writeFile (dir / "counts.tsv") (String.join counts.toList)
  IO.println s!"styles {total} files; {isolated.length} isolated configurations; {products.length} full products; {Forms.all.length} forms at 4 depths; JSON and wire oracles beside every file"

end Tools.Styles
