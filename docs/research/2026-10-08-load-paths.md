# Load paths in the proof graph: what carries the claims, and what waits for a load

Status: research note (history, not authority). Base: `c8d7b066` (`refactor/phase1-phase3`), the
fast-forward merge of Codex's fold slice, which every measurement below includes.
Tool: `tools/Tools/LoadPaths.lean` (`#load_report`, `#load_map`).

On 2026-10-08 the owner offered an analogy, and asked to probe and mechanize it in this session.
Early structural steel was used everywhere, and buildings were heavier than stone. Engineering
then learned to place it on load paths, and sparse, strong structures followed. The proof graph
is dense in the same way, and the work now is consolidation: enclose the edges, and reconfigure
the supports. The owner added a constraint. No member is removed before we know its use: support, an access
point, or part of the engineering basis.

## 1. The one thing to know first

- **The analogy holds, and it is measurable.** A theorem carries load when a registered claim
  rests on it. The tool counts that over the whole proof graph from the proof terms.
- **Three numbers, for the loaded proof graph of `Effect4.Laws`:**
  - 13,139 authored theorems; 6,226 are under a registered root, or are one;
  - 3,392 are used by some theorem, but no registered root reaches them;
  - 3,521 are used by no theorem. Of these, 1,694 are hand-written, untagged for `simp`, and not
    named in any battery or tool.
- **No member is removed on this evidence** (owner, 2026-10-08). "Unconsumed" means "carries no
  load under the claims registered today". It is a reason to look, not to cut (§5).
- **A landing has a reuse ratio.** Today's repair of decisions row 333 reuses 6 laws against 8
  new helpers, and all 10 of its theorems carry load. The shared step laws reuse at 71%.

## 2. The literature

Read from abstracts and summaries on 2026-10-08, not from full texts.

| Work | What it gives here |
| --- | --- |
| Michell, *The limits of economy of material in frame-structures*, Philosophical Magazine 8 (1904) | least-weight frames are fully stressed: every member carries load. The numerical method starts from a dense "ground structure" of all possible members, and removes the idle ones for a given set of load cases |
| Blanchette, Haslbeck, Matichuk and Nipkow, *Mining the Archive of Formal Proofs*, CICM 2015 | a proof library's dependency graph, measured: size, dependencies and reuse across entries |
| Huch, *Structure in Theorem Proving* (arXiv 2209.13305, 2022) | the in-degree of the archive's dependency graph appears scale-free: a few joints carry most of the use |
| Li, Peng, Severini and Shafto, *The Network Structure of Mathlib* (arXiv 2604.24797, 2026) | 308,129 declarations and 8.4 million edges. Separate the edges the compiler synthesizes from the explicit ones. Namespaces couple at 50.9%, and an import is used at a median of 1.6% |
| Kaliszyk, Urban and Vyskočil, *Lemmatization for Stronger Reasoning in Large Theories*, FroCoS 2015, and the lemma mining over HOL Light before it | only a small part of what a library proves is named and reused; mining the inference graph finds the lemmas worth naming |
| Ringer, Palmskog, Sergey, Gligoric and Tatlock, *QED at Large* (2019) | proof engineering as software engineering: reuse, repair, regression; lemmas stand in for tests, with no coverage measure |
| Hierarchy Builder (Cohen, Sakaguchi and Tassi, 2020), packed classes (Garillot, Gonthier, Mahboubi and Rideau, 2009) | a structure's theory is proved once and applies to every instance; small factories, built into the larger structures: laws at the algebra |

**The point the owner made, in Michell's terms.** The ground structure method removes a member
only against a fixed set of load cases. A member idle under one case may carry another. The proof
graph's load cases are its claims, and the registered ones are not all of them. Planned claims,
an agent's questions, and the module law (G10) are load cases still to come.

## 3. The definitions

| Word | Definition, as the tool computes it |
| --- | --- |
| direct dependency | an authored theorem that a theorem's proof term names, through the generated auxiliaries |
| root | a registry claim's pointer, or a requirement's top node (`Tools.Semantics.registry`) |
| load-bearing | a root reaches it along direct dependencies |
| unconsumed | no theorem of the loaded tree names it, and it is no root |
| off the roots' paths | some theorem names it, but no root reaches it |
| reuse ratio of a landing | its edges into the tree outside it, over those and its edges into itself |
| joints of a landing | the tree theorems it names most |

Edges into Lean's own library and into instances that type-class resolution chose are counted
apart: they are plumbing, as the Mathlib study separates compiler-synthesized edges.

## 4. Measurements

The environment imports `Effect4.Laws`. The batteries under `Test/` are not loaded, because
loading them would rebuild them after the session repair of row 333. So the battery consumers
were found by name, in the sources.

**Landings.**

| Landing | Theorems | Load-bearing | Reuse ratio | Its main joints |
| --- | --- | --- | --- | --- |
| `Laws.Program.Typing.Parts` (row 333's repair) | 10 | 10 | 42% | `callAt_rowTy`, `checkModule_sound`, `hasTy_focusAt` |
| `Laws.Modules.Step` (with Codex's fold slice) | 97 | 55 | 71% | `ItemResults.all_cons`, `Reads.eval`, `FieldRef.read_law` |
| `Laws.Program.Typing.{Focus,Replace,Table}` | 32 | 20 | 45% | `effTy_sound`, `effTy_complete`, `check_sound` |
| `Laws.Program.Sketch` | 18 | 8 | 43% | `check_restrict`, `check_ext`, `check_complete` |
| `Laws.Modules.Queue` (with Codex's fold slice) | 311 | 168 | 45% | `Reads.to` (20), `nodesFormed_of_check`, `normalize_list_canonical` |

**The unconsumed theorems, by what consumes them.**

| Class | Count |
| --- | --- |
| used by no theorem of the loaded graph | 3,521 |
| of these, named in a battery under `Test/` | 1,124 |
| named in a tool under `tools/` | 209 |
| named nowhere | 2,188 |
| of these, tagged for `simp` | 128 |
| of the rest, in a generated file | 297 |
| hand-written | 1,694 |

The largest hand-written families: `Pool.Model.types_*` (20), `RunFiberOk.frame_*` (15),
`Queue.Model.types_*` (15), `Pool.Model.reads_*` (11), `RunMachineOk.frame_*` (11),
`Refinement.projects_*` (11), `GuardState.frame_*` (10).

## 5. What it means, before any member moves

Each family of unconsumed theorems is triaged into one of four classes. No class removes anything
by itself.

| Class | Test | Then |
| --- | --- | --- |
| access | an agent or an author asks for it: a characterization of a definition, a frame lemma of one field | keep; register it as an access lemma, so the graph counts it |
| basis | it completes a family whose other members carry load, so the family is a total interface | keep; its load is the family's |
| subsumed | a shared law now states it, at the algebra (`Step.typed` over a module's per-operation typing) | keep until a connector shows the shared law gives it; then retire it, with the connector as the record |
| stale | it speaks of a representation that the tree replaced | retire with the representation |

The per-field frame families look like basis. The per-operation `types_*` and `reads_*` families of
the Queue and the Pool stayed unconsumed after Codex's shared step laws merged. They look like
candidates for subsumption by those laws. Both
readings are hypotheses, not findings.

The 3,392 theorems used off the roots' paths are a placement question first: a claim that rests on
them may be missing from the registry.

## 6. The gauge, and the meta-interface

- **The gauge.** Each landing's receipt reports its reuse ratio, its load-bearing count, and its
  joints. A consolidation phase should show the ratio rising, and the unconsumed count not
  growing without a class.
- **The meta-interface.** For an agent, the roots are the interface of the proof graph, and the
  joints are its deep modules. `#explain` can report each theorem's load-bearing status and its
  class, as data, beside its placement.

## 6a. Prediction before a slice (cutover slice S1, 2026-10-08)

A slice's top theorems are written first, with each new lemma left as a planned goal. Their proofs
then name what the slice reuses and what it still owes. `#landing_plan T` walks from the tops
through their own modules. It sorts what it reaches into goals owed, local steps, and the tree's
joints with their load-bearing standing. After the landing, `#landing_plan` and `#load_report` measure
the same quantities.

| Slice | Predicted | Landed |
| --- | --- | --- |
| S1b, the sketch's table and refusals | 1 goal owed, with its one step named; 4 local steps; 6 joints, all load-bearing; reuse 54% | the 2 owed lemmas, the same 4 steps and the same 6 joints; the 2 proofs reused no tree theorem |
| the splice law (`edit-splices-table`) | 11 goals owed; 2 local steps; 7 joints, 6 load-bearing; reuse 35% | the 11, and 4 more: three general list facts and one step split out of the environments' casework; 12 joints, the 5 more being the typed-replacement and checker laws that the two hard goals used; reuse 54% by edges; one heartbeat raise |
| S1a, the sketch's focus and fill (measured after) | not predicted | sketch laws 50% reuse, parts laws 60%; joints: the module check's soundness, `focusAt_typed`, `hasTy_replace_focusAt` |
| the edit session over a program (`edit-session-coherent`, first form) | 5 goals owed; 2 local steps; 6 joints, all load-bearing; reuse 46% | the 5, and no other lemma; 9 joints, the 3 more (`focusAt_eq_some`, `focusAt_nil`, `table_head`) forecast in words; reuse 66% by edges |
| the view and repaint tops, written as bare goals | 2 goals owed; 0 local steps; 0 joints | a bare goal names nothing, so the plan predicts nothing; each top was sketched, then proved from the landed steps |
| the splice over a whole program's parts (`module-table-splices`, `module-annotate-table`) | 14 goals owed; 4 local steps; 15 joints, all load-bearing; reuse 45% | the 14, and 7 more: five entry and address facts and the two spine edits forecast in words; 24 joints, 7 of the 9 more forecast in words; reuse 57% by edges; no heartbeat raise |
| H1 on a whole program (`module-holes-conservative`) | 1 goal owed; 2 local steps; 3 joints; reuse 50% | exactly the prediction: the one goal, no other lemma, the same 3 joints |
| the omission's splice (`omit-splices-table`) | 6 goals owed, one behind another goal; 3 local steps; 10 joints; reuse 55% | the 6, and small steps: the converse of the focus law (forecast in words), the focus's program, an entry's path, a key step, the bodies' case; 30 joints, the 20 more the extension's field laws that the algebra's agreement reads (forecast in words); reuse 68% |

The prediction was exact because the decomposition went down to the new lemmas. Its cost is the
statements and the skeleton of the proof; the leaves are the work it predicts.

Four readings of the four predictions:

- **The owed goals are exact** when the decomposition reaches the new lemmas. A bare goal predicts
  nothing: write the top's proof modulo its steps first.
- **The joints are undercounted** by the leaves' own proofs. A forecast in words, written before
  the proofs, named 15 of the 17 joints that the plan missed.
- **The unforecast lemmas are small facts**: list facts, address facts, one entry at a spine. Seat
  ORG's address module and list homes (`docs/research/2026-10-08-seat-ORG-theory-map.md`, ranks 1
  and 4) would turn them into joints.
- **Reuse rises from the plan to the landing**, from 35 to 54, 46 to 66, 45 to 57 and 55 to 68
  percent.
- **The plan stops at a module's border and at a goal.** A goal behind a joint of another module,
  or behind another goal, is not listed. Name a top in each module of the slice.

**The same reading on an area before work starts.** The session's laws are
`Laws.Api.HostSession`, `Laws.Api.SessionMeaning` and `Laws.Run`. They hold 142 theorems, 59
load-bearing and 45 unconsumed. Their reuse is 18%: 152 local edges against 35 into the tree, and
897 into Lean's own library.
Their strongest joints are small option facts. So a session slice that plans today should expect
little reuse, unless shared laws of runs and journals are factored first. The lowering's Lean half
(`src/OCaml5`) is outside the tool's scopes, and joins them when the tool reads it.

## 7. What this note does not establish

- The load is counted along proof terms. An `aesop` bank's rule leaves a trace only through the
  term that the search built. A battery's `simp` use of an untagged lemma is not seen.
- Battery consumers were found by name in the sources, not from proof terms.
- The roots are the semantics registry's. A claim that is stated but not registered counts as no load.
- The literature was read from abstracts and summaries. No full text is filed here.
- Nothing was removed.
