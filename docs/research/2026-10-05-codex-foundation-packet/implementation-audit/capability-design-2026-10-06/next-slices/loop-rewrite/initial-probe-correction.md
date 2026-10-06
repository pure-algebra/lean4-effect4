# Scratch fixture correction

The first Python mirror attempt stopped before producing results.
The finalizer fixture reused a loop whose cursor occupied slot zero.
The finalizer itself binds the delivered exit at slot zero.
The corrected fixture places its cursor at slot one.
The mirror now treats a wrong numeric argument as its source-style shape failure.
A deliberate unshifted-insertion control retains the distinction.
This was a scratch-model fixture error, not an Effect4 source finding or a Lean result.
