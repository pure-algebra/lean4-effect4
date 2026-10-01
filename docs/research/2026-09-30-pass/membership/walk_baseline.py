"""Build the mechanical baseline for Walk.lean: the slice-5 declarations that mention the old
value judgments, copied from the tree at their exact line ranges, with names renamed only.
`python3 walk_baseline.py <repo root> > baseline.lean`; then `diff baseline.lean <(sed ... Walk.lean)`
counts the lines a migration to `Fits` changes beyond the renaming."""
import re, sys
root = sys.argv[1]
def lines(path, a, b):
    return open(f"{root}/{path}").read().split("\n")[a - 1:b]
SEGMENTS = [
    ("src/Effect4/Laws/Program/Typed/Admission.lean", 77, 80),    # EnvTyped
    ("src/Effect4/Laws/Program/Typed/Admission.lean", 90, 119),   # PointTyped, BodyTyped, strongExit_success
    ("src/Effect4/Laws/Program/Typed/Admission.lean", 127, 168),  # strongExit_of_clean, cleanExit_of_never
    ("src/Effect4/Laws/Program/Typed/Residual.lean", 34, 86),     # storePre, storePost, Ψ_S
    ("src/Effect4/Laws/Program/Typed/Residual.lean", 116, 259),   # fiberPre, fiberPost, Ψ_F, TypedProg, inversions
    ("src/Effect4/Laws/Program/Typed/Residual.lean", 261, 308),   # hook protocols
    ("src/Effect4/Laws/Program/Typed/Residual.lean", 319, 344),   # settling_ref_allocation
    ("src/Effect4/Laws/Program/Typed/Residual.lean", 358, 387),   # settling_fork, settling_mask
    ("src/Effect4/Laws/Program/Typed/Stack.lean", 20, 42),        # HookLaws, WalkTyped
    ("src/Effect4/Laws/Program/Typed/Stack.lean", 86, 336),       # failure lemma, walk, hooks
    ("src/Effect4/Laws/Program/Typed/Stack.lean", 340, 349),      # saveAnswerR_typed
    ("src/Effect4/Laws/Program/Typed/Stack.lean", 359, 373),      # deliver_active
    ("src/Effect4/Laws/Program/Typed/Assembly.lean", 33, 73),     # CompletionStrong … TypedState
    ("src/Effect4/Laws/Program/Typed/Assembly.lean", 78, 97),     # AnswerOk, QueueOk, StepPreserves
    ("src/Effect4/Laws/Program/Typed/Assembly.lean", 101, 139),   # envTyped_append, capture_lookup
    ("src/Effect4/Laws/Program/Typed/Residual.lean", 389, 433),   # M3a…, M3bWorld obligations
    ("src/Effect4/Laws/Program/Typed/Stack.lean", 385, 425),      # M4Stack, M5Hooks obligations
    ("src/Effect4/Laws/Program/Typed/Assembly.lean", 146, 229),   # M3bAssembly, M6Ledger obligations
]
RENAME = [
    ("StrongValue", "StrongValueF"), ("StrongExit", "FitsExit"), ("ServicesOk", "ServicesFitE"),
    ("EnvTyped", "EnvTypedF"), ("PointTyped", "PointTypedF"), ("BodyTyped", "BodyTypedF"),
    ("storePre", "storePreF"), ("storePost", "storePostF"), ("Ψ_S", "Ψ_SF"),
    ("fiberPre", "fiberPreF"), ("fiberPost", "fiberPostF"), ("Ψ_F", "Ψ_FF"),
    ("TypedProg", "TypedProgF"), ("IteratorProtocol", "IteratorProtocolF"),
    ("IteratorAnswer", "IteratorAnswerF"), ("LoopProtocol", "LoopProtocolF"),
    ("LoopAnswer", "LoopAnswerF"), ("frameProtocols", "frameProtocolsF"), ("HookLaws", "HookLawsF"),
    ("WalkTyped", "WalkTypedF"), ("walk_saved", "walk_savedF"), ("walk_done", "walk_doneF"),
    ("popR_typed", "popR_typedF"), ("popR_typed_interpR", "popR_typed_interpRF"),
    ("hookLaws_interpR", "hookLaws_interpRF"), ("saveAnswerR_typed", "saveAnswerR_typedF"),
    ("deliver_active", "deliver_activeF"), ("strongExit_success", "fitsExit_success"),
    ("strongExit_of_clean", "fitsExit_of_clean"), ("cleanExit_of_never", "cleanExit_of_never_fits"),
    ("strongExit_failure_of_error", "fitsExit_failure_of_error"),
    ("unguard_payload_inv", "unguard_payload_invF"),
    ("finishFinalizer_payload_inv", "finishFinalizer_payload_invF"),
    ("settling_ref_allocation", "settling_ref_allocationF"), ("settling_fork", "settling_forkF"),
    ("settling_mask", "settling_maskF"), ("strongValue_bool_true", "strongValue_bool_trueF"),
    ("strongExit_bool", "strongExit_boolF"), ("CompletionStrong", "CompletionStrongF"),
    ("CaptureTyped", "CaptureTypedF"), ("preds", "predsF"), ("TypedState", "TypedStateF"),
    ("AnswerOk", "AnswerOkF"), ("QueueOk", "QueueOkF"), ("StepPreserves", "StepPreservesF"),
    ("envTyped_append", "envTyped_appendF"), ("capture_lookup", "capture_lookupF"),
]
def rename(text):
    for a, b in RENAME:
        text = re.sub(r"(?<![\w.])" + re.escape(a) + r"(?![\w])", b, text)
    return re.sub(r"(?<![.\w])World(?![.\w])", "W", text)
out = []
for path, a, b in SEGMENTS:
    out.append(f"-- {path}:{a}-{b}")
    out.extend(rename("\n".join(lines(path, a, b))).split("\n"))
    out.append("")
print("\n".join(out))
