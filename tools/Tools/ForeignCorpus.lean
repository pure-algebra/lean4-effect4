import Tools.Styles
import Test.Program.Gen
import OCaml5.Eff.Emit

/-! Strict foreign fixtures are constructed before rendering and before either reader.
The seeded structural skeletons are assigned literal failures/provisions and dense keys.
This is a new corpus; the existing printer-image corpus is unchanged. -/
namespace Tools.ForeignCorpus
open Effect4 Effect4.Program
abbrev Keys := List (ServiceKey × ServiceKey)
abbrev Build := StateM Keys

def key (old : ServiceKey) : Build ServiceKey := do
  let keys ← get
  match keys.find? (fun p => p.1 == old) with
  | some p => return p.2
  | none =>
    let service := if old.service.value == 5 then 5 else if old.service.value == 6 then 6 else 4
    let fresh : ServiceKey := ⟨⟨keys.length + 4⟩, ⟨service⟩⟩
    set (keys ++ [(old, fresh)])
    return fresh

def literal (t : Term) : Lit := match t with | .lit l => l | _ => .nat 0
def provision (k : ServiceKey) : Lit :=
  if k.service.value == 5 then .bool true else if k.service.value == 6 then .unit else .nat 0

mutual
  def program : Eff NativeOp → Build (Eff NativeOp)
    | .succeed t => pure (.succeed t)
    | .fail t => pure (.fail (.lit (literal t)))
    | .yieldError t => pure (.yieldError t)
    | .failCause c => pure (.failCause c)
    | .sync t => pure (.sync t)
    | .suspend b => return .suspend (← program b)
    | .perform op t => pure (.perform op t)
    | .callback op t => pure (.callback op t)
    | .bind a b => return .bind (← program a) (← program b)
    | .gen b => return .gen (← statements b)
    | .catchCause a b => return .catchCause (← program a) (← program b)
    | .matchCause a b c => return .matchCause (← program a) (← program b) (← program c)
    | .onExit a b => return .onExit (← program a) (← program b)
    | .exit a => return .exit (← program a)
    | .uninterruptible a => return .uninterruptible (← program a)
    | .interruptible a => return .interruptible (← program a)
    | .branch t a b => return .branch t (← program a) (← program b)
    | .whileLoop i t s b => return .whileLoop i t s (← program b)
    | .yieldNow n => pure (.yieldNow n)
    | .awaitFiber t m => pure (.awaitFiber t m)
    | .withFiber a => return .withFiber (← action a)
    | .scoped a => return .scoped (← program a)
    | .acquireRelease a b => return .acquireRelease (← program a) (← program b)
    | .choose n a b => return .choose n (← program a) (← program b)
    | .provideLayer l isLocal b => do
      let b ← program b
      let l ← layer l
      return .provideLayer l isLocal b
    | .service k => return .service (← key k)
    | .provideService k _ b => do
      let b ← program b
      let k ← key k
      return .provideService k (.lit (provision k)) b
  def statement : Stmt NativeOp → Build (Stmt NativeOp)
    | .bindYield e => return .bindYield (← program e)
    | .yieldDiscard e => return .yieldDiscard (← program e)
    | .ret t => pure (.ret t)
    | .ifElse t a b => return .ifElse t (← statements a) (← statements b)
    | .whileTrue b => return .whileTrue (← statements b)
    | .breakLoop => pure .breakLoop
  def statements : Stmts NativeOp → Build (Stmts NativeOp)
    | .nil => pure .nil
    | .cons a b => return .cons (← statement a) (← statements b)
  def programs : Effs NativeOp → Build (Effs NativeOp)
    | .nil => pure .nil
    | .cons a b => return .cons (← program a) (← programs b)
  def action : ActionTerm NativeOp → Build (ActionTerm NativeOp)
    | .fork p o => return .fork (← program p) o
    | .forkIn p o s => return .forkIn (← program p) o s
    | .forkScoped p o => return .forkScoped (← program p) o
    | .raceAll ps => return .raceAll (← programs ps)
    | x => pure x
  def layer : LayerTerm NativeOp → Build (LayerTerm NativeOp)
    | .succeed k _ => do let k ← key k; return .succeed k (provision k)
    | .effect k b => return .effect (← key k) (← program b)
    | .effectDiscard b => return .effectDiscard (← program b)
    | .provide a b => return .provide (← layer a) (← layer b)
    | .provideMerge a b => return .provideMerge (← layer a) (← layer b)
    | .merge a b => return .merge (← layer a) (← layer b)
    | .fresh a => return .fresh (← layer a)
    | .orDie a => return .orDie (← layer a)
    | .ref t => pure (.ref t)
    | .mergeAll ls => return .mergeAll (← layers ls)
  def layers : LayerTerms NativeOp → Build (LayerTerms NativeOp)
    | .nil => pure .nil
    | .cons a b => return .cons (← layer a) (← layers b)
end

def keyJson (keys : Keys) : String :=
  "[" ++ ",".intercalate (keys.map fun (_, k) =>
    "{\"ordinal\":" ++ toString k.name.value ++ ",\"service\":" ++ toString k.service.value ++
    ",\"sourceId\":\"k" ++ toString k.name.value ++ "_" ++ toString k.service.value ++ "\"}") ++ "]\n"

/-- Every profile row has a construction, independent of random seed coverage. -/
def nativeProbes : List (String × Eff NativeOp) :=
  OCaml5.Eff.allOps.zipIdx.map fun (op, index) =>
    let row := op.row
    let request : Term := match row.request with
      | .unit => .lit .unit
      | .nat => .lit (.nat 0)
      | .prod _ _ => .app "pair" (.cons (.var 0) (.cons (.lit (.nat 0)) .nil))
      | _ => .var 0
    let p := if row.kind == .async then Eff.callback op request else Eff.perform op request
    let p := match row.request with
      | .handle name => .bind (.perform (if name == NativeOp.refTarget then .refMake else .deferredMake) (.lit (.nat 1))) p
      | .prod (.handle name) _ => .bind (.perform (if name == NativeOp.refTarget then .refMake else .deferredMake) (.lit (.nat 1))) p
      | _ => p
    ("native-" ++ toString index ++ "-" ++ row.name ++ "-" ++ "-".intercalate row.trailing, p)

def corpus (dir : System.FilePath) (skeletons : List (String × Eff NativeOp)) : IO Unit := do
  IO.FS.createDirAll dir
  let mut index := "name\tstyle\tbytes\n"
  let mut counts := "style\tfiles\n"
  let mut total := 0
  for c in Tools.Styles.isolated do
    let mut count := 0
    for (name, skeleton) in skeletons ++ Tools.Styles.probes ++ nativeProbes do
      let .ok kept := roundTrip nativeSignature nativeSpell 0 skeleton | throw (IO.userError s!"skeleton refused {name}")
      let (p, keys) := (program kept).run []
      -- The style renderer uses only names and values, never the main declaration's
      -- annotation. Hoisting is the library printer's operation; the oracle stays p.
      let .ok module := printModule nativeSignature "program" ⟨.unit, .never, .empty⟩ p
        | throw (IO.userError s!"construction refused {name}")
      let some main := module.getLast? | throw (IO.userError s!"construction empty {name}")
      let declarations := module.dropLast.map fun d =>
        (d.name, Codegen.Styles.expression c.config d.value)
      let .ok recovered := roundTrip nativeSignature nativeSpell 0 p | throw (IO.userError s!"construction unreadable {name}")
      unless recovered == p do throw (IO.userError s!"construction not canonical {name}")
      let name := c.name ++ "-" ++ name
      IO.FS.writeFile (dir / (name ++ ".keys.json")) (keyJson keys)
      index := index ++ (← Tools.Styles.write dir name c
        (Codegen.Styles.expression c.config main.value) p false declarations)
      count := count + 1
    for f in Codegen.Forms.all do
      for n in [0, 1, 2, 5] do
        let some p := f.example n | throw (IO.userError s!"form absent {f.id}")
        let (same, keys) := (program p).run []
        unless same == p do throw (IO.userError s!"form outside strict construction {f.id}")
        let some expr := Codegen.Styles.Form.foreign f c.config n | throw (IO.userError s!"form source absent {f.id}")
        let name := s!"{c.name}-form-{f.id}-{n}"
        IO.FS.writeFile (dir / (name ++ ".keys.json")) (keyJson keys)
        index := index ++ (← Tools.Styles.write dir name c expr p (f.id == "yieldKey"))
        count := count + 1
    counts := counts ++ s!"{c.name}\t{count}\n"
    total := total + count
  let .ok p := roundTrip nativeSignature nativeSpell 0 Tools.Styles.composite | throw (IO.userError "composite oracle")
  let .ok printed := print nativeSignature 0 p | throw (IO.userError "composite source")
  for c in Tools.Styles.products do
    IO.FS.writeFile (dir / (c.name ++ ".keys.json")) "[]\n"
    index := index ++ (← Tools.Styles.write dir c.name c (Codegen.Styles.expression c.config printed) p)
    counts := counts ++ s!"{c.name}\t1\n"
    total := total + 1
  IO.FS.writeFile (dir / "index.tsv") index
  IO.FS.writeFile (dir / "counts.tsv") counts
  IO.println s!"foreign {total}; isolated {Tools.Styles.isolated.length}; products {Tools.Styles.products.length}; forms {Codegen.Forms.all.length} at four depths; construction JSON/wire/keys before readers"
end Tools.ForeignCorpus
