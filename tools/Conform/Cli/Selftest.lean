import Conform.Core.Evidence
import Conform.Core.Report
import Conform.Core.Policy
import Conform.Core.Obligation

/-!
# Conform.Cli.Selftest — the core's own contract, checked by the build

Every claim the core's module headers make that is not a theorem is a `#guard` here, so
`lake build Conform` fails when one stops holding. Nothing here is specific to Effect4.

| claim | guard |
| --- | --- |
| the exit code is `0` iff complete and all pass, `1` on refusal or counterexample, `2` on unresolved or incomplete | `exit_*` |
| JSON object keys come out sorted, whatever order they were built in | `json_sorted` |
| `Policy.object` refuses an unknown key and names it with its path | `policy_unknown_key` |
| `Policy.field` refuses a missing required key; `field?` reads absence as `none` | `policy_missing`, `policy_optional` |
| `Policy.nat` refuses a negative or fractional number | `policy_nat` |
| `Obligation.validate` refuses an unregistered kind and names it | `obligation_kind` |
| a duplicate cannot hide a missing subject | the duplicate and unexpected guards |
-/

namespace Conform.Selftest

open Lean (Json)

def subj (n : String) : Subject := ⟨"declaration", [n]⟩

def passRow (n : String) (e : Evidence := .tested) : Row := Row.pass "t.check" (subj n) e "ok"
def refusedRow (n : String) : Row := Row.refused "t.check" (subj n) "bad"
def unresolvedRow (n : String) : Row := Row.unresolved "t.check" (subj n) "missing input"
def ceRow (n : String) : Row := Row.counterexample "t.check" (subj n) "witness" (Json.str "w")

def report (rows : List Row) (expected : Nat := rows.length) : Report :=
  { tool := "selftest", expected, required := #[⟨"t.check", subj "a"⟩, ⟨"t.check", subj "b"⟩],
    rows := rows.toArray }

-- exit codes
#guard (report [passRow "a", passRow "b"]).exitCode = 0
#guard (report [passRow "a", refusedRow "b"]).exitCode = 1
#guard (report [passRow "a", ceRow "b"]).exitCode = 1
#guard (report [passRow "a", unresolvedRow "b"]).exitCode = 2
#guard (report [refusedRow "a", unresolvedRow "b"]).exitCode = 2   -- unresolved outranks refused
#guard (report [passRow "a"] (expected := 2)).exitCode = 2         -- a dropped subject is visible
#guard (report []).exitCode = 2                                     -- zero expected, zero rows

-- Coverage is a bijection, not a count. These caught the original false acceptance.
#guard (report [passRow "a", passRow "a"]).exitCode = 2
#guard (report [passRow "a", passRow "c"]).exitCode = 2
#guard ({ tool := "selftest", expected := 0, required := #[], rows := #[] } : Report).complete
#guard (⟨"check", ⟨"kind", ["a/b"]⟩⟩ : CheckId) != ⟨"check", ⟨"kind", ["a", "b"]⟩⟩

#guard Evidence.ofString? "verified" = none
#guard Outcome.ofString? "ok" = none

-- JSON keys sorted regardless of insertion order
def unsorted : Json := Json.mkObj [("zeta", Json.num 1), ("alpha", Json.num 2), ("mid", Json.num 3)]
#guard (match unsorted with | .obj kvs => kvs.keys | _ => []) = ["alpha", "mid", "zeta"]

-- the report's JSON carries the summary and every row
#guard (match (report [passRow "a", refusedRow "b"]).toJson.getObjVal? "summary" with
  | .ok s => ((s.getObjVal? "refused" |>.toOption) == some (Json.num 1)) &&
             ((s.getObjVal? "exit" |>.toOption) == some (Json.num 1))
  | .error _ => false)

-- policy: unknown key refused with its path
def objUnknown : Json := Json.mkObj [("name", Json.str "x"), ("cover", Json.arr #[])]
#guard (match Policy.run (Policy.at_ "families" (Policy.index 3
    (Policy.object objUnknown ["name", "mode"]))) with
  | .error msg => msg == "$.families[3]: unknown key `cover` (known: name, mode)"
  | .ok _ => false)

-- policy: missing required key refused; optional absence is none
def objName : Json := Json.mkObj [("name", Json.str "x")]
#guard (match Policy.run (do
    let get ← Policy.object objName ["name", "mode"]
    Policy.field get "mode" Policy.string) with
  | .error msg => msg == "$: missing required key `mode`"
  | .ok _ => false)
#guard (match Policy.run (do
    let get ← Policy.object objName ["name", "mode"]
    Policy.field? get "mode" Policy.string) with
  | .ok none => true
  | _ => false)
#guard (match Policy.run (do
    let get ← Policy.object objName ["name", "mode"]
    Policy.field get "name" Policy.string) with
  | .ok "x" => true
  | _ => false)

-- policy: naturals only
#guard (Policy.run (Policy.nat (Json.num 3))).toOption = some 3
#guard (Policy.run (Policy.nat (Json.num (-1)))).toOption = none
#guard (Policy.run (Policy.nat (Json.str "3"))).toOption = none
#guard (Policy.run (Policy.enum (Json.str "exhaustive") [("exhaustive", true), ("default", false)])).toOption = some true
#guard (Policy.run (Policy.enum (Json.str "strict") [("exhaustive", true), ("default", false)])).toOption = none

-- obligations: unregistered kinds refused
def registry : Obligation.Registry := [⟨"representation.image-missing", "no Image for the element"⟩]
def ob (k : String) : Obligation :=
  { kind := k, subject := subj "T", status := .unproved, statement := "…" }
#guard (Obligation.validate registry #[ob "representation.image-missing"]).toOption = some ()
#guard (match Obligation.validate registry #[ob "made.up"] with
  | .error msg => msg.startsWith "obligation kind `made.up`"
  | .ok _ => false)
#guard (match (report [passRow "a"]).withObligations registry #[ob "representation.image-missing"] with
  | .ok j => (j.getObjVal? "obligations").toOption.isSome
  | .error _ => false)

end Conform.Selftest
