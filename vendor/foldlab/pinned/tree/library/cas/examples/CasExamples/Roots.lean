import Cas

/-!
# Roots — publication, executed

The rooted language (`StoreSig`) run over grammar-built content under
the production digest: the seeded word admits, a program that
publishes the journal's root and lists the roots answers exactly that
root while leaving the word untouched, and publishing an address the
word does not bind is refused fail-closed with nothing published.
-/

namespace CasExamples.Roots

open Cas Cas.Lang Cas.Grammar

/-- The drawer, on the page — grammar surface syntax. -/
def myDrawer : Tree .entry := journal% [
  save% "hello.txt" := "hello world"
]

/-- The seeded word, under the production digest. -/
def w0 : Word := myDrawer.flatten sha256Addr

def rootAddr : Addr32 := myDrawer.address sha256Addr

/-- Publish the journal's root, then list the published roots. -/
def publishAndList : Prog StoreSig (List Addr32) := do
  publish rootAddr
  listRoots

/-- An address the word does not bind. -/
def absent : Addr32 := sha256Addr (utf8 "nowhere")

def expect (label : String) (condition : Bool) : IO Unit := do
  unless condition do
    throw (IO.userError s!"Roots check failed: {label}")

def checks : IO Unit := do
  expect "seeded word admits" (Word.wf w0)
  match runRooted sha256Addr 10 publishAndList (w0, []) with
  | (.done rs, (w', roots)) => do
    expect "publish-then-list answers the published root"
      (rs == [rootAddr])
    expect "roots grew by exactly the published root"
      (roots == [rootAddr])
    expect "the word is untouched by publication" (w' == w0)
  | _ => throw (IO.userError "publish-and-list did not complete")
  match runRooted sha256Addr 10 (publishAndList) ([], []) with
  | (.refused _, (_, roots)) =>
    expect "publishing over an empty word admits no root" (roots == [])
  | _ => throw (IO.userError "publishing over an empty word was not refused")
  match runRooted sha256Addr 10 (publish absent) (w0, []) with
  | (.refused _, (w', roots)) => do
    expect "absent publish publishes nothing" (roots == [])
    expect "absent publish leaves the word untouched" (w' == w0)
  | _ => throw (IO.userError "publishing an absent address was not refused")
  IO.println s!"roots ok: 1 root published over {w0.length} bindings, absent publish refused"

#eval checks

end CasExamples.Roots
