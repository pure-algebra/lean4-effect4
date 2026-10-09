import Effect4.Laws.Api.SessionMeaning

set_option autoImplicit false
set_option maxRecDepth 8192

namespace HostGeneralizationReview
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote
open Effect4.Program.Agreement

-- Finite controls for the generalized H8 proof. No production theorem is added.
def table : RowTable :=
  [{ name := "left", spelling := "H.left", kind := .async, registration := .external,
     request := .nat, answer := .nat, error := .prod .string .string, cite := "review" },
   { name := "right", spelling := "H.right", kind := .async, registration := .external,
     request := .nat, answer := .nat, error := .prod .string .string, cite := "review" }]

abbrev Log := List (Nat × Nat)
def failure : ExitV := .failure (.fail (.tagged "E" "body"))

def recording : Effects.Comodel (RowSig table) Log where
  answer op log := match op.2 with
    | .nat n =>
      let result := if op.1.val = 0 && n = 7 then failure
        else .success (.nat (n + 10 * op.1.val + log.length))
      some (result, log ++ [(op.1.val, n)])
    | _ => none

def once : Effects.Comodel (RowSig table) Log where
  answer op log := if log.length = 0 then recording.answer op log else none

def num (n : Nat) : Term := .lit (.nat n)
def call (row : Nat) (request : Term) : NativeEff := .perform (.external row) request

def chain : NativeEff := .bind (call 0 (num 2)) (call 1 (.var 0))
def cleanup : NativeEff := .onExit (call 0 (num 7)) (call 1 (num 9))
def recovery : NativeEff := .catchCause (call 0 (num 7)) (call 1 (num 9))

-- Distinct rows, actual request values, and the state from the preceding answer affect results.
def meaning (host : Effects.Comodel (RowSig table) Log) (p : NativeEff) :
    Option (ExitV × Log × Bool) :=
  (hostRun host p [] Stores.empty []).map fun r =>
    (r.1, r.2.2, decide (r.2.1 = Stores.empty))

-- Tags: 0 exhausts the execution budget; 1 waits; 2 returns an exit.
def localView (host : Effects.Comodel (RowSig table) Log) (p : NativeEff)
    (compileFuel executionFuel : Nat) : Nat × Option (ExitV × Log × Bool) :=
  match localRunC host p executionFuel (fiberOf (compile p compileFuel) []) Stores.empty [] with
  | none => (0, none)
  | some .waits => (1, none)
  | some (.exit ex stores log) => (2, some (ex, log, decide (stores = Stores.empty)))

#guard StraightRows table chain
#guard StraightRows table cleanup
#guard StraightRows table recovery
#guard meaning recording chain = some (.success (.nat 13), [(0, 2), (1, 2)], true)
#guard localView recording chain 10 100 = (2, some (.success (.nat 13), [(0, 2), (1, 2)], true))
-- Negative control: replacing the second request with a fixed value must change the answer.
#guard meaning recording (.bind (call 0 (num 2)) (call 1 (num 3))) =
  some (.success (.nat 14), [(0, 2), (1, 3)], true)
#guard meaning recording cleanup = some (failure, [(0, 7), (1, 9)], true)
#guard localView recording cleanup 10 100 = (2, some (failure, [(0, 7), (1, 9)], true))
#guard meaning recording recovery = some (.success (.nat 20), [(0, 7), (1, 9)], true)
#guard localView recording recovery 10 100 = (2, some (.success (.nat 20), [(0, 7), (1, 9)], true))

-- Declining the second request is a waiting frontier, independently of execution exhaustion.
#guard meaning once chain = none
#guard localView once chain 10 100 = (1, none)
#guard localView recording chain 10 0 = (0, none)
-- A zero compile budget produces a spinning frontier, even with an answering host.
#guard localView recording chain 0 100 = (0, none)
#guard match localRunC (silentHost table) (call 0 (num 2)) 10
    (fiberOf (compile (call 0 (num 2)) 10) []) Stores.empty () with
  | some .waits => true
  | _ => false

#eval ([chain, cleanup, recovery].map fun p =>
  let result := localView recording p 10 100
  (result.1, result.2.map fun r => r.2))
#eval [(localView once chain 10 100).1,
       (localView recording chain 10 0).1, (localView recording chain 0 100).1]
end HostGeneralizationReview
