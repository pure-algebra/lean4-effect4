import Lean

/-!
The proof-style ratchet (`AGENTS.md`: "Not written by hand in a new or touched proof, anywhere
under `src/`: `simp_all`, `first | …` and `try`"; "A hand-written `simp` names its lemmas as
`simp only [...]`").

The scan parses each source file with the parser tables of the environment it runs in, so it
reads syntax kinds, not spellings. The four kinds are `Lean.Parser.Tactic.simpAll`,
`Lean.Parser.Tactic.first`, the `try` macro (`Lean.Parser.Tactic.tacticTry_`) and
`Lean.Parser.Tactic.simp` without `only`. A comment, a string or a `try … catch` of `do`
notation is never counted. Occurrences are counted per file, declaration and kind, and compared
with a committed baseline that records the occurrences written before the rule:

- a count above its baseline entry, or an occurrence with no entry, is refused: a new use;
- an entry whose count went down or whose occurrences are gone is refused as stale, so the
  baseline cannot outlive its reason, as the axiom gate's exemptions cannot;
- `#proof_style_record` rewrites the baseline, which makes any change to it a reviewed diff.

The declaration is the first `declId` of the command; a command without one (an `example`, an
unnamed instance) is keyed by its command kind. A command the parser cannot read (syntax local to
its file, or a scoped syntax whose namespace the scan does not open) is an occurrence of kind
`unread`, recorded like the others: an old gap is accepted by its baseline entry, a new unread
command is refused, since banned uses inside it would go uncounted.
This reflection is tooling only; it never enters stored program content.
-/
namespace ProofGraph.ProofStyle
open Lean Parser Elab Command

/-- The banned kind of one syntax node, if any. -/
def bannedKind (stx : Syntax) : Option String :=
  if stx.isOfKind ``Lean.Parser.Tactic.simpAll then some "simp_all"
  else if stx.isOfKind ``Lean.Parser.Tactic.first then some "first"
  else if stx.isOfKind `Lean.Parser.Tactic.tacticTry_ then some "try"
  else if stx.isOfKind ``Lean.Parser.Tactic.simp && stx[3].isNone then some "simp-without-only"
  else none

/-- Every banned node under `stx`, on an explicit stack. -/
def occurrences (stx : Syntax) : Array (String × Syntax) := Id.run do
  let mut out : Array (String × Syntax) := #[]
  let mut stack := #[stx]
  -- each node is visited once; the bound is a loop bound
  for _ in [0:100000000] do
    let some s := stack.back? | break
    stack := stack.pop
    if let some k := bannedKind s then out := out.push (k, s)
    stack := stack ++ s.getArgs
  return out

/-- The key of a command: its first declared name, or its command kind. -/
def commandKey (cmd : Syntax) : String :=
  match cmd.find? (·.isOfKind ``Lean.Parser.Command.declId) with
  | some d => d[0].getId.toString
  | none => s!"<{cmd.getKind}>"

structure Occurrence where
  file : String
  decl : String
  kind : String
  line : Nat
  deriving Inhabited

/-- Scan one file: its occurrences, an unread command among them as kind `unread`. -/
def scanFile (env : Environment) (path : System.FilePath) : IO (Array Occurrence) := do
  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input path.toString
  let (_, state, messages) ← Parser.parseHeader inputCtx
  let pmctx : ParserModuleContext := { env, options := {} }
  let mut st := state
  let mut msgs := messages
  let mut out : Array Occurrence := #[]
  for _ in [0:1000000] do
    let before := msgs.toList.length
    let (cmd, st', msgs') := Parser.parseCommand inputCtx pmctx st msgs
    st := st'
    msgs := msgs'
    if Parser.isTerminalCommand cmd then break
    let line := (inputCtx.fileMap.toPosition (cmd.getPos?.getD 0)).line
    if msgs.toList.length > before then
      out := out.push { file := path.toString, decl := commandKey cmd, kind := "unread", line }
    for (k, s) in occurrences cmd do
      let at_ := (inputCtx.fileMap.toPosition (s.getPos?.getD 0)).line
      out := out.push { file := path.toString, decl := commandKey cmd, kind := k, line := at_ }
  return out

/-- Every `.lean` file under `dir`, sorted. -/
def leanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let files ← dir.walkDir
  return (files.filter (·.extension == some "lean")).qsort (·.toString < ·.toString)

/-- The counts per `(file, declaration, kind)`. -/
def counts (occs : Array Occurrence) : Std.HashMap (String × String × String) Nat :=
  occs.foldl (init := {}) fun m o =>
    m.insert (o.file, o.decl, o.kind) (m.getD (o.file, o.decl, o.kind) 0 + 1)

def parseBaseline (text : String) : Std.HashMap (String × String × String) Nat :=
  (text.splitOn "\n").foldl (init := {}) fun m line =>
    match line.splitOn "\t" with
    | [file, decl, kind, n] => m.insert (file, decl, kind) n.toNat!
    | _ => m

def renderBaseline (c : Std.HashMap (String × String × String) Nat) : String :=
  let rows := c.toArray.map fun ((file, decl, kind), n) => s!"{file}\t{decl}\t{kind}\t{n}"
  "\n".intercalate (rows.qsort (· < ·)).toList ++ "\n"

private def scanAll (dir : String) : CommandElabM (Array Occurrence) := do
  let env ← getEnv
  let mut occs : Array Occurrence := #[]
  for f in ← leanFiles dir do
    occs := occs ++ (← scanFile env f)
  return occs

/-- `#proof_style_check "dir" "baseline"`: refuse a new use or a stale baseline entry. A pass
prints nothing; `#proof_style_record` reports the counts. -/
syntax (name := proofStyleCheck) "#proof_style_check " str str : command

@[command_elab proofStyleCheck] def elabProofStyleCheck : CommandElab := fun stx => do
  let some dir := stx[1].isStrLit? | throwError "proof style: expected a directory"
  let some baselinePath := stx[2].isStrLit? | throwError "proof style: expected a baseline path"
  let occs ← scanAll dir
  let now := counts occs
  let base := parseBaseline (← IO.FS.readFile baselinePath)
  let mut problems : Array String := #[]
  let keyText (k : String × String × String) : String := s!"{k.1}\t{k.2.1}\t{k.2.2}"
  for ((file, decl, kind), n) in now.toArray.qsort (fun a b => keyText a.1 < keyText b.1) do
    let allowed := base.getD (file, decl, kind) 0
    if n > allowed then
      let lines := (occs.filter fun o => o.file == file && o.decl == decl && o.kind == kind).map (·.line)
      problems := problems.push <| if kind == "unread" then
          s!"new unread command: {decl} ({file}, lines {lines.toList}): the scan cannot parse it, so banned uses in it go uncounted; {n} > {allowed} recorded"
        else s!"new use: {kind} in {decl} ({file}, lines {lines.toList}); {n} > {allowed} recorded"
  for ((file, decl, kind), n) in base.toArray.qsort (fun a b => keyText a.1 < keyText b.1) do
    let found := now.getD (file, decl, kind) 0
    if found < n then
      problems := problems.push s!"stale entry: {kind} in {decl} ({file}): {found} < {n} recorded; rerun #proof_style_record"
  unless problems.isEmpty do
    throwError "proof style: {problems.size} finding(s)\n{"\n".intercalate problems.toList}"

/-- `#proof_style_record "dir" "baseline"`: write the baseline from the tree as it stands. -/
syntax (name := proofStyleRecord) "#proof_style_record " str str : command

@[command_elab proofStyleRecord] def elabProofStyleRecord : CommandElab := fun stx => do
  let some dir := stx[1].isStrLit? | throwError "proof style: expected a directory"
  let some baselinePath := stx[2].isStrLit? | throwError "proof style: expected a baseline path"
  let occs ← scanAll dir
  IO.FS.writeFile baselinePath (renderBaseline (counts occs))
  let unread := (occs.filter (·.kind == "unread")).size
  logInfo m!"proof style: recorded {occs.size - unread} uses and {unread} unread commands"

end ProofGraph.ProofStyle
