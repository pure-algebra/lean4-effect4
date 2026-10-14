import Effect4.Program.Compile

open Effect4 Effect4.Machine Effect4.Program

-- Finite controls for the proposed constant-exit law's context arms.
#guard (compileEff (.provideContext (.var 0) (.succeed (.lit .unit)))
  { path := [], env := [], fuel := 4, tape := [] }).asExit? = (badShape : NCode).asExit?
#guard (compileEff (.provideService ⟨⟨0⟩, ⟨0⟩⟩ (.var 0) (.succeed (.lit .unit)))
  { path := [], env := [], fuel := 4, tape := [] }).asExit? = (badShape : NCode).asExit?
