import Cas.Lang.Sig
import Cas.Lang.Prog
import Cas.Lang.Ops
import Cas.Lang.Interp
import Cas.Lang.Handler
import Cas.Lang.Auth
import Cas.Lang.Tower
import Cas.Lang.Representation
import Cas.Lang.Roots
import Cas.Lang.Worded
import Cas.Lang.WordWire
import Cas.Lang.TreeProg
import Cas.Lang.Defun
import Cas.Lang.Fragments

/-!
# The program grammar — layer 3 of the language

Programs as operation trees over effect signatures. `Sig` makes a
language a value and composes languages by sum; `Prog` is the free
monad of continuations over a signature; `Ops` is the store language
(`put`/`load`/`fail`) and the LLM extension (`infer`); `Interp` is
one-step interpretation over the store word, calling the proved
admission judgment, with the L5–L7 agreement and preservation laws;
`Roots` is the publication extension (`RootSig`, the sum `StoreSig`,
and the rooted interpreter delegating Cas operations to `step`);
`Worded` is the history extension (`WordSig` speaking `since`, the sum
`WordedSig`, and the worded interpreter delegating store operations to
`stepRooted` — `since_suffix`, `since_zero`, `since_cas_agrees`,
`stepWorded_preserves_wf`, and the feed laws `since_next`,
`since_compose`, `runWorded_preserves_wf`), with `WordWire` carrying the
word's wire records — the receipt and the history document the
`emitword` gate mirrors into the effects package;
`TreeProg` is layer 2 derived inside layer 3 — the grammar term as a
store program, with `putTree_correct` (F1) proving the run computes
exactly the elaboration's address and store, deduplicating shared
subterms (F2); `Auth` is authenticated computation as a handler pair —
`proveHandler` records the LOAD trace onto a proof word, `verifyHandler`
re-interprets the same program against a claimed proof word holding no
store, `verify_load_or_collision` is the one-operation
ideal-or-collision disjunct at hash-lattice Level 0, and
`whole_run_security` (W-SEC) with `whole_run_correctness` (W-COR)
lifts the pair to a whole program — still Level 0, with the collision
exhibited and the verifier's prefix consumption placed outside the
disjunction per ADSF.

`Fragments` carries no definitions: it is the FRAGMENT TOWER, the
interop reference model — the ladder `PProg ⊂ the guarded table ⊂ Prog`
ordered by expressive power, each rung with its static-analysis status,
store encoding, handler set, and agreement theorems by name, plus what
another effect system may assume when it consumes one. Read it before
coding against a CAS program. Do not confuse it with `Tower`, which is
the orthogonal SERVICE tower (a handler implemented as a program over a
lower signature).
-/
