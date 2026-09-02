# Case 04: a frozen proof and an executable witness

Use `$lean-reification-proof` to assess this proof repair request and deliver
a written repair handoff. No source changes or tool installation are permitted
in this exercise; the mathematical data below are complete.

The frozen theorem says that every checked program has the same final natural
number from the same initial state, regardless of the supplied answer tape.
The checked language has an operation `askBit`, followed by a branch returning
2 for `false` and 3 for `true`. Both one-answer tapes are compatible and complete.
The program is admitted by the frozen checker. The allowed edit fence is proof
bodies and proved private helper lemmas; changing the statement or admitted
programs requires a contract amendment. A proposed quick fix is to make the
checker reject this program or introduce a private axiom for deterministic
answers. Neither change has been authorized.

Separately, an existing proof establishes `there exists a program realizing
formula F` as an existential proposition. The user wants to save and execute
the witness and suggests pattern-matching on this proof to get the program
data. No computational witness interface or source-proof translation has been
implemented. The project already has canonical first-order program data and
does not want a new syntax.

What can be completed within the fence? What is the decisive evidence and the
precise upstream handoff? Keep theorem existence, program extraction, and host
execution separate, and preserve legitimate approved classical reasoning.
