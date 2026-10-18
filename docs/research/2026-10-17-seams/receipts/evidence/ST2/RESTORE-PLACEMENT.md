# Checked image recovery

A checked legacy image can retain generation two when a new duplicate trace retains generation one.
The control in `test_control.ml` retains this difference.
A recovered image therefore needs its own admitted event rather than an invented commit history.

1. Concept: `translation-simulation`, the checked disk image used by adapter observations; R13.
2. Questions: `cas-restore-roots` and `cas-restore-closed`, compatibility and preservation.
   `Effect4.Store.restore_roots` and `Effect4.Store.restore_closed` are their planned pointers.
   The goals live in `src/Effect4/Laws/Store/Recovery.lean` before proof work.
3. Reach: the canonical restore event starts only at an empty store.
   Node admission uses the existing shared node check in order.
   Root admission checks unique names and each target's durable resident kind.
   Success retains exact root records, including legacy generations.
4. Exclusions: historical ancestry, past generation provenance, hash injectivity, filesystem correctness, and host progress.
   Recovery admits a checked image; it reconstructs no lost event journal.
5. Consumers: ST4 `Exchange.load` and `Exchange.apply` take the resulting canonical `Cas`.
   S6 uses the same disk-to-Cas connector after reopening.

The node-closure helper serves checked image admission.
The root equality law serves exact preservation of the recovered generation table.
The native comparison and kill harness remain finite host evidence.

`RecoveryImage.nodes` holds decoded Node data, not raw disk bytes.
`RecoveryImage.read` reads every raw node through `Node.read` before constructing that data.
`Cas.restoreBytes` uses `RecoveryImage.read` before `Cas.restore`.
Native `Disk.image` also checks each recorded address against its bytes before semantic admission.
That address failure is `Fault (Corrupt address)`, outside the semantic refusal type.
The raw-byte control must refuse a malformed node before any derived store state exists.


`cas-restore-targets` is the preservation question for each recovered root's durable resident kind.
`Effect4.Store.restore_targets` is its planned pointer in the same law module.
Its reach and exclusions match the two checked image questions above.
`checkImageRoots_resolves` serves that pointer and the ST4/S6 checked-image consumers.
