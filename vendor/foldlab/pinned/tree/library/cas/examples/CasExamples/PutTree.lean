import Cas

/-!
# Put-tree — F1 and F2, executed

`putTree_correct` (F1) says a grammar term's program, run with
node-count-plus-one fuel over any honest admissible word, completes at
exactly the term's fold address and grows the word by a SUBLIST of
`flatten` — shared subterms deduplicate through `put`'s duplicate
outcome (F2). The checks below run both halves through the interpreter
at build time under the production digest:

- a share-free tree's run appends exactly `size` bindings (the sublist
  is all of `flatten`), admits, and answers the root node at the root
  address through the bridge;
- a tree with one shared chunk runs to a word STRICTLY shorter than
  `flatten` — the dedup, observed;
- replaying the same program over its own output is inert: same
  address, same word, binding for binding.
-/

namespace CasExamples.PutTree

open Cas Cas.Lang Cas.Grammar

/-- A two-leaf blob over two DISTINCT chunks: no sharing, so the run
can deduplicate nothing. -/
def chunkA : Tree .chunk := .chunk (Payload.utf8 "0123456789abcdef")
def chunkB : Tree .chunk := .chunk (Payload.utf8 "ghijklmnopqrstuv")
def distinctTree : Tree .manifest :=
  .manifest 1 32 2 (.parent (.leaf 0 16 chunkA) (.leaf 1 16 chunkB))

/-- Two leaves over ONE shared chunk: `flatten` carries the chunk's
binding twice, but the program admits it once. -/
def sharedChunk : Tree .chunk := .chunk (Payload.utf8 "one chunk, twice")
def sharedTree : Tree .tree :=
  .parent (.leaf 0 16 sharedChunk) (.leaf 1 16 sharedChunk)

/-- Run a term's program with the theorem's fuel over a given word. -/
def runPut (tr : Tree t) (w : Word) : Status CasSig Addr32 × Word :=
  run sha256Addr (tr.size + 1) tr.prog w

def expect (label : String) (condition : Bool) : IO Unit := do
  unless condition do
    throw (IO.userError s!"PutTree check failed: {label}")

def checks : IO Unit := do
  -- (a) no sharing: the run from empty IS flatten's word
  let wDistinct ← match runPut distinctTree [] with
    | (.done a, w') => do
      expect "distinct: done at the fold address"
        (a == distinctTree.address sha256Addr)
      expect "distinct: no dedup possible — word length is size"
        (w'.length == distinctTree.size)
      expect "distinct: the run's word admits" (Word.wf w')
      expect "distinct: the bridge answers the root node at the root"
        (Word.toStore w' (distinctTree.address sha256Addr)
          == some (distinctTree.node sha256Addr))
      pure w'
    | _ => throw (IO.userError "distinct tree program did not complete")
  -- (b) shared chunk: the run's word is strictly shorter than flatten
  let wShared ← match runPut sharedTree [] with
    | (.done a, w') => do
      expect "shared: done at the fold address"
        (a == sharedTree.address sha256Addr)
      expect "shared: flatten length is size"
        ((sharedTree.flatten sha256Addr).length == sharedTree.size)
      expect "shared: deduplication observed — word shorter than size"
        (w'.length < sharedTree.size)
      expect "shared: the run's word admits" (Word.wf w')
      pure w'
    | _ => throw (IO.userError "shared tree program did not complete")
  -- (c) replay inertness: the same program over its own output
  match runPut sharedTree wShared with
  | (.done a, w'') => do
    expect "replay: done at the same address"
      (a == sharedTree.address sha256Addr)
    expect "replay: the word is unchanged, binding for binding"
      (w'' == wShared)
  | _ => throw (IO.userError "replay of shared tree did not complete")
  -- (d) summary
  IO.println s!"put-tree ok: distinct {distinctTree.size} → {wDistinct.length} bindings, shared {sharedTree.size} → {wShared.length} (deduped {sharedTree.size - wShared.length}), replay inert"

#eval checks

end CasExamples.PutTree
