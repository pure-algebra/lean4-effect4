import Cas

/-!
# The agent step — a program of the language

The agent step is NOT a primitive — it is a program: load the history,
refuse a non-agent-step, fold the context with `foldlM` (reduction free
from the monad), `infer` against the folded prompt, and admit exactly
three nodes — context, output, agent step. The inference answer enters
only as recorded content; admission is the only gate; the attestation
is the executor's claim, never a proof.

## The sort the third node rides (decision 40)

That third node used to be a journal `entry` (`0x0C`), which was
latitude the `entry` row explicitly granted — "the codec constrains a
reference's expected tag, never the arity". It cost the one thing this
program's records exist for: with the form riding the journal's tag, an
edge expecting an AGENT STEP specifically was unspellable, because
references type-check at tag granularity. Decision 40 ratified `agent`
(`0x49`) for exactly this form, and the migration is one byte per edge
— attestation, context, output, prev, all unchanged — plus a genesis
for the chain to bottom out at, on the `entry.genesis` precedent. The
chain a step extends is now a chain of agent steps rather than a branch
of the journal, which is what "who did this" needs to be a typed walk.

Content is seeded through the grammar (`journal%`/`save%`), flattened
to a word under the production digest with the chain's genesis appended,
and every check below runs at build time through the interpreter: the
seeded word admits, the step appends exactly three bindings and
preserves admission, a dangling history refuses before anything is
admitted, and a wrong-kind history — a `file`, or the journal entry
this form used to ride — refuses at the guard.
-/

namespace CasExamples.AgentStep

open Cas Cas.Lang Cas.Grammar

def textOf (bs : Bytes) : String :=
  (String.fromUTF8? (ByteArray.mk bs.toArray)).getD s!"<{bs.length}B binary>"

/-- An opaque value node. -/
def valueNode (payload : Bytes) : Node :=
  ⟨schemeVersion, Ty.value.wireTag, payload, []⟩

/-- A context node: no payload, one typed edge per folded item. -/
def contextNode (refs : List Ref) : Node :=
  ⟨schemeVersion, Ty.context.wireTag, [], refs⟩

/-- An agent step: the attestation note and its three typed edges. -/
def agentNode (note : Bytes) (refs : List Ref) : Node :=
  ⟨schemeVersion, Ty.agent.wireTag, note, refs⟩

/-- An agent chain's first step: no attestation, no edges. The `prev`
edge below expects this sort, so the chain has to bottom out, and this
is where — `entry.genesis`'s move at the sort that took the form off
`entry`'s tag. -/
def agentGenesis : Node := ⟨schemeVersion, Ty.agent.wireTag, [], []⟩

/-- One agent step, as a program of the agent language. -/
def agentStep (history : Addr32) (contextIds : List Addr32)
    (attestation : Bytes) : Prog AgentSig Addr32 := do
  let prev ← liftCas (load history)
  liftCas (require (prev.tag == Ty.agent.wireTag) "history is not an agent step")
  let links ← liftCas <| contextIds.foldlM (init := []) fun acc a => do
    let o ← load a
    pure (acc ++ [Ref.mk o.tag a])
  let ctx ← liftCas (put (contextNode links))
  let prompt ← liftCas <| contextIds.foldlM (init := "") fun acc a => do
    let o ← load a
    pure (acc ++ textOf o.payload ++ "\n")
  let answer ← infer prompt
  let out ← liftCas (put (valueNode (utf8 answer)))
  liftCas (put (agentNode attestation
    [⟨Ty.context.wireTag, ctx⟩, ⟨Ty.value.wireTag, out⟩,
     ⟨Ty.agent.wireTag, history⟩]))

/-- Deterministic oracle for the demo run. -/
def scripted (prompt : String) : String :=
  s!"folded {prompt.length} chars; ship it"

/-- The drawer, on the page — grammar surface syntax. -/
def helloFile : Tree .file := save% "hello.txt" := "hello world"

def myDrawer : Tree .entry := journal% [
  save% "hello.txt" := "hello world",
  save% "ideas.md" := "# merkle to merkle"
]

/-- The chain's first step, addressed under the production digest. -/
def genesisAddr : Addr32 := sha256Addr (encodeNode agentGenesis)

/-- The seeded word, under the production digest: the drawer, then the
agent chain's genesis. The genesis carries no edges, so appending it
preserves the children-first admission discipline. -/
def w0 : Word := myDrawer.flatten sha256Addr ++ [⟨genesisAddr, agentGenesis⟩]

def demoRun : Status CasSig Addr32 × Word :=
  runAgent sha256Addr scripted 100
    (agentStep genesisAddr
      [helloFile.address sha256Addr]
      (utf8 "model=scripted;t=0"))
    w0

def expect (label : String) (condition : Bool) : IO Unit := do
  unless condition do
    throw (IO.userError s!"AgentStep check failed: {label}")

def checks : IO Unit := do
  expect "seeded word admits" (Word.wf w0)
  match demoRun with
  | (.done _, w') => do
    expect "step appends exactly three bindings"
      (w'.length == w0.length + 3)
    expect "admission preserved across the run" (Word.wf w')
  | _ => throw (IO.userError "agent step did not complete")
  match runAgent sha256Addr scripted 100
      (agentStep (sha256Addr (utf8 "nope")) [] []) w0 with
  | (.refused _, w') =>
    expect "dangling history admits nothing" (w'.length == w0.length)
  | _ => throw (IO.userError "dangling history was not refused")
  match runAgent sha256Addr scripted 100
      (agentStep (helloFile.address sha256Addr) [] []) w0 with
  | (.refused _, _) => pure ()
  | _ => throw (IO.userError "wrong-kind history was not refused")
  -- The tag this form used to ride is now just another wrong kind: a
  -- journal entry is not an agent step, and the guard says so.
  match runAgent sha256Addr scripted 100
      (agentStep (myDrawer.address sha256Addr) [] []) w0 with
  | (.refused _, _) => pure ()
  | _ => throw (IO.userError "a journal entry was accepted as an agent history")
  IO.println s!"agent step ok: {w0.length} → {w0.length + 3} bindings"

#eval checks

end CasExamples.AgentStep
