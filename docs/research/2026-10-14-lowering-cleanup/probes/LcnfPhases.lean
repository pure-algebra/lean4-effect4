import Lean
import Conform.Lcnf.Validity
import OCaml5.Ml.Syntax
import OCaml5.Ml.Render
import OCaml5.Ml.Check
import OCaml5.Lcnf.Externs
import OCaml5.Lcnf.Types
import OCaml5.Lcnf.Translate

/-!
# LC-4's phase probe: one LCNF artifact's generation, timed phase by phase

It takes the argv of one artifact of `ocaml/gen/roots.json`, as `scripts/generate.py` builds it,
and runs the steps of `OCaml5.Tools.LcnfGen` in its order. Each step prints its wall time.
Two steps are measured beside the generator's own: one walk with the settled carrier table
(`translateClosure`), and the translation of each closure declaration alone (`translateDecl`).
Their difference is the walk without the translation. It writes nothing.

A pure step's result is printed before the clock is read again. The compiler may move a pure
binding to its first use, and the print is that use, so the clock reads after the step.

    lake env lean -DwarningAsError=true -M4096 --run \
      docs/research/2026-10-14-lowering-cleanup/probes/LcnfPhases.lean <an artifact's argv>
-/

open Lean OCaml5 OCaml5.Lcnf

structure Args where
  out : String := ""
  types : Array Name := #[]
  cap : Nat := 60
  roots : Array Name := #[]
  imports : Array Name := #[]
  externs : Option String := none
  prelude : Option String := none

def parseArgs : List String → Args → Args
  | "--out" :: p :: rest, a => parseArgs rest { a with out := p }
  | "--types" :: ts :: rest, a =>
    parseArgs rest { a with types := a.types ++ ((ts.splitOn ",").map String.toName).toArray }
  | "--cap" :: n :: rest, a => parseArgs rest { a with cap := n.toNat! }
  | "--import" :: m :: rest, a =>
    parseArgs rest { a with imports := a.imports ++ ((m.splitOn ",").map String.toName).toArray }
  | "--externs" :: p :: rest, a => parseArgs rest { a with externs := some p }
  | "--prelude" :: p :: rest, a => parseArgs rest { a with prelude := some p }
  | r :: rest, a => parseArgs rest { a with roots := a.roots.push r.toName }
  | [], a => a

def ms (a b : Nat) : String :=
  let tenths := (b - a) / 100000
  s!"{tenths / 10}.{tenths % 10} ms"


/-- A copy of `collectClosure`'s walk with a clock around each of its parts. A pure part's result
is read by a branch before the clock is read again, so the part runs before the read. -/
def timedWalk (roots : Array Name) (cap : Nat) (tn : TypeNames) (ex : Externs) :
    CoreM (Array (String × Nat)) := do
  let env ← getEnv
  let mono := Conform.Lcnf.persistedMonoIndex env
  let mut tLookup := 0
  let mut tFlow := 0
  let mut tTranslate := 0
  let mut tCallees := 0
  let mut done : NameSet := {}
  let mut queue : Array Name := roots
  let mut decls := 0
  let mut pops := 0
  let mut i := 0
  while i < queue.size do
    let n := queue[i]!
    i := i + 1
    pops := pops + 1
    let a0 ← IO.monoNanosNow
    let skip := done.contains n || ex.hasFn n || (builtin? n).isSome ||
      (env.find? n matches some (.ctorInfo _)) || decls ≥ cap
    if skip then
      let a1 ← IO.monoNanosNow
      tLookup := tLookup + (a1 - a0)
      continue
    done := done.insert n
    let some d := mono.findIn? env n | continue
    let a1 ← IO.monoNanosNow
    tLookup := tLookup + (a1 - a0)
    let f1 := ClockFlow.ofDecl d
    if f1.deps.size == 123456789 then IO.println "never"
    let mut d := d
    let mut userName := n
    match redArgTarget? d with
    | some twin =>
      done := done.insert twin
      if let some dt := mono.findIn? env twin then
        d := dt
        let f2 := ClockFlow.ofDecl dt
        if f2.deps.size == 123456789 then IO.println "never"
    | none =>
      userName := stripRedArg n
      if userName != n then
        done := done.insert userName
        if let some wrapper := mono.findIn? env userName then
          let f3 := ClockFlow.ofDecl wrapper
          if f3.deps.size == 123456789 then IO.println "never"
    let a2 ← IO.monoNanosNow
    tFlow := tFlow + (a2 - a1)
    let (t, st) := translateDecl env d userName (globalName userName) tn ex
    if t.callees.size + st.calls.size == 123456789 then IO.println "never"
    let a3 ← IO.monoNanosNow
    tTranslate := tTranslate + (a3 - a2)
    decls := decls + 1
    for callee in st.calls do
      unless done.contains callee do
        if stripRedArg callee == callee then
          if (mono.findIn? env (callee ++ `_redArg)).isSome then pure ()
        queue := queue.push callee
    let a4 ← IO.monoNanosNow
    tCallees := tCallees + (a4 - a3)
  return #[("lookups", tLookup), ("clock flows", tFlow), ("translation", tTranslate),
    ("callees", tCallees), ("declarations", decls * 1000000), ("queue pops", pops * 1000000)]

def main (argv : List String) : IO Unit := do
  let t0 ← IO.monoNanosNow
  initSearchPath (← findSysroot)
  let args := parseArgs argv {}
  let ex : Externs ← match args.externs with
    | none => pure {}
    | some path => do
      match Externs.parse (← IO.FS.readFile path) with
      | .ok e => pure e
      | .error msg => throw (IO.userError s!"{path}: {msg}")
  let preludeText : Option String ← match args.prelude with
    | none => pure none
    | some path => pure (some (← IO.FS.readFile path))
  let env ← importModules (args.imports.map fun m => { module := m }) {} 0
  let t1 ← IO.monoNanosNow
  IO.println s!"phase import: {ms t0 t1}"
  let ctx : Core.Context :=
    { fileName := "<lcnf-phases>", fileMap := default, maxHeartbeats := 1000000 * 1000 }
  let act : MetaM Unit := do
    let mut tn : TypeNames := {}
    let a0 ← IO.monoNanosNow
    let (closure0, ex0, inferred0) ← translateClosureInferring args.roots args.cap tn ex
    let a1 ← IO.monoNanosNow
    IO.println s!"phase closure with inference: {ms a0 a1} \
      ({closure0.decls.size} declarations, {inferred0.size} inferred rows)"
    -- one walk with the settled table: the cost of one round
    let one ← translateClosure args.roots args.cap tn ex0
    let a2 ← IO.monoNanosNow
    IO.println s!"phase one walk with the settled table: {ms a1 a2} ({one.decls.size} declarations)"
    let env ← getEnv
    let mono := Conform.Lcnf.persistedMonoIndex env
    IO.println s!"the mono index: {mono.size} entries"
    let a3w ← IO.monoNanosNow
    IO.println s!"phase the mono index alone: {ms a2 a3w}"
    let parts ← timedWalk args.roots args.cap tn ex0
    let a3 ← IO.monoNanosNow
    IO.println s!"phase the timed walk: {ms a3w a3}"
    for (label, nanos) in parts do IO.println s!"  part {label}: {ms 0 nanos}"
    -- the translation alone: each closure declaration once, through `translateDecl`
    let mut work := 0
    let mut pairs : Array (Translated × St) := #[]
    for t in closure0.decls do
      let some d := mono.findIn? env t.leanName | throwError s!"no mono declaration: {t.leanName}"
      let (t', st) := translateDecl env d t.userName t.ocamlName tn ex0
      work := work + t'.callees.size + st.calls.size
      pairs := pairs.push (t', st)
    IO.println s!"translation work: {work}"
    let a4m ← IO.monoNanosNow
    IO.println s!"phase translation alone: {ms a3 a4m}"
    -- the walk's merges of each declaration's state into the closure, as `collectClosure` does them
    let pushNew (a : Array Name) (n : Name) : Array Name := if a.contains n then a else a.push n
    let mut c : Closure := {}
    for (t, st) in pairs do
      c := { c with
        decls := c.decls.push t,
        realTypes := st.realTypes.foldl pushNew c.realTypes,
        mentioned := st.mentioned.foldl pushNew c.mentioned,
        usedExterns := st.usedExterns.foldl (fun a k => if a.contains k then a else a.push k) c.usedExterns,
        usedOps := st.usedOps.foldl (fun a o => if a.contains o then a else a.push o) c.usedOps,
        usedCargs := st.usedCargs.foldl pushNew c.usedCargs,
        wantedCargs := st.wantedCargs.foldl (fun a w => if a.contains w then a else a.push w) c.wantedCargs,
        toLists := c.toLists ++ st.toLists,
        todos := c.todos ++ st.todos }
    IO.println s!"merged: {c.realTypes.size} real types, {c.mentioned.size} mentioned, \
      {pairs.foldl (fun n (_, st) => n + st.mentioned.size) 0} mentions, {c.usedExterns.size} externs"
    let a4 ← IO.monoNanosNow
    IO.println s!"phase the walk's merges: {ms a4m a4}"
    let mut flows : Array ClockFlow.Flow := #[]
    for t in closure0.decls do
      if let some d := mono.findIn? env t.leanName then flows := flows.push (ClockFlow.ofDecl d)
    IO.println s!"clock flows: {flows.size}, {flows.foldl (fun n f => n + f.deps.size) 0} dependencies"
    let a4b ← IO.monoNanosNow
    IO.println s!"phase clock flows of the declarations: {ms a4 a4b}"
    let refused := ClockFlow.refusals env args.roots flows
    IO.println s!"clock refusals: {refused.size}"
    let a5 ← IO.monoNanosNow
    IO.println s!"phase clock refusals: {ms a4b a5}"
    let mut closure := closure0
    let exs := ex0
    let mut gen ← generate (closure.realTypes ++ args.types) closure.mentioned tn exs
    let a6 ← IO.monoNanosNow
    IO.println s!"phase types: {ms a5 a6} ({gen.decls.size} type declarations)"
    let mut passes := 0
    for _ in [:4] do
      if gen.collisions.isEmpty then break
      passes := passes + 1
      for (_, _, n) in gen.collisions do tn := tn.insert n (fullTypeName n)
      closure ← retranslate closure tn exs
      gen ← generate (closure.realTypes ++ args.types) closure.mentioned tn exs
    let a7 ← IO.monoNanosNow
    IO.println s!"phase collision passes: {ms a6 a7} ({passes} passes)"
    let emitted ← match emit closure.decls with
      | .ok items => pure items
      | .error message => throwError message
    IO.println s!"emitted items: {emitted.length}"
    let a8 ← IO.monoNanosNow
    IO.println s!"phase emission: {ms a7 a8}"
    let body : List Ml.Decl :=
      [gen.item, .blank]
        ++ (match preludeText with | none => [] | some t => [.rawD t, .blank])
        ++ emitted
    let items : List Ml.Decl :=
      if args.externs.isNone then
        [.floatingAttrD "warning \"-26-27-30-32-33-35-37-39-69\"", .blank] ++ body
      else
        [.floatingAttrD "warning \"-26-27-30-32-33-35-37-39-69\"", .blank,
         .rawD carrierSignatures, .blank,
         .moduleD "Make" carrierParams body]
    let m : Ml.Module := { name := "probe", header := some "probe", items := items }
    let mono2 := Conform.Lcnf.persistedMonoIndex env
    let mut rows := 0
    for t in closure.decls do
      let some d := mono2.findIn? env t.leanName | throwError s!"no mono declaration: {t.leanName}"
      let census := Conform.Lcnf.Census.ofDecl {} d
      rows := rows + (Conform.Lcnf.constructs.map (fun k => census.get k)).foldl (· + ·) 0
        + (hash d).toNat % 2
    IO.println s!"manifest work: {rows}"
    let a9 ← IO.monoNanosNow
    IO.println s!"phase manifest: {ms a8 a9}"
    let diags := Ml.checkModule m
    IO.println s!"checkModule diagnostics: {diags.length}"
    let a10 ← IO.monoNanosNow
    IO.println s!"phase checkModule: {ms a9 a10}"
    let captures := hygieneProblems closure.decls
    IO.println s!"hygiene problems: {captures.length}"
    let a11 ← IO.monoNanosNow
    IO.println s!"phase hygiene: {ms a10 a11}"
    let text := Ml.render m
    IO.println s!"rendered characters: {text.length}"
    let a12 ← IO.monoNanosNow
    IO.println s!"phase rendering: {ms a11 a12}"
  let _ ← (act.run' {}).toIO ctx { env := env }
  let t2 ← IO.monoNanosNow
  IO.println s!"phase total after start: {ms t0 t2}"
