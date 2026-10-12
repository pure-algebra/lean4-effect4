# Target adapters for the two-field machine cut

The checked R1 source cut precedes target regeneration.
This plan updates its existing OCaml adapters in the same target pass as multiplication.

Concept: translation-simulation, R8.
Question: the generated engine consumes the current machine record fields.
Role: target adapter maintenance for the existing compiler and engine comparisons.
Consumer: the generated `Api_engine` and its reference and native instances.

`Dispatcher.mk` now has one stored field: its buckets.
The checked closure erases that constructor and reaches the existing insert operation.
The [refined dispatcher plan](DispatcherPlan.md) retains the type row and converts only tracked empty lists.
The nominal field-row attempt remains a retained rejection.

The retained finite `armedOf` observation now reads whether the owner's buckets are nonempty.
Read the same observation from the existing `f_dispatcher` projection in the engine renderer.
Remove the duplicate instance projection of the deleted Boolean.
The machine's actual scheduled-owner queue remains `RunMachine.armed`.
The target libraries' independent host-flag API keeps its own finite controls.
No claim identifies that API's arbitrary flag states with the amended Lean record.

Regenerate every LCNF root from its producer and manifest.
Build the engine, reference instance, comparison driver, and benchmark through the pinned OCaml switch.
Run finite dispatcher and engine controls after the regeneration.
Retain warning 8 and repair any exposed compiler coverage at its producer.
These controls do not establish a whole-runtime simulation.
