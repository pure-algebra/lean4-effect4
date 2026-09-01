// Ordinary TypeScript sees the erased service. Suppress it so the dedicated
// Effect diagnostic is the sole expected signal.
// @ts-expect-error
export const missingContext: Effect.Effect<User, WriteEmailError> =
  email.replace("new@example.test", source)
