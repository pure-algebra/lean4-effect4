module
public import Effect4.Library.Ref.Model
public import Effect4.Program.Authoring.Rows
public import Effect4.Step.Callback

/-!
# Ref: the native cell operations and typed step callbacks

The thirteen effectful operations use the existing `Program.Authoring.Ref` forms.
`Step.callback` supplies a stored step to a native callback and captures its outer inputs.
The independent model is `Ref.Model`; its laws are in `Effect4.Laws.Library.Ref.Operations`.

No cell record or operation family is added. `Ref.set` retains the native cell-identity reply
(DI-98); use `Forms.asVoid` from `Effect4.Author` for the declared-void observation.
The direct host operations `makeUnsafe` and `getUnsafe` are outside this effectful surface.
-/
