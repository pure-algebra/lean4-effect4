// Ordinary TypeScript sees the erased error. Suppress it so the dedicated
// Effect diagnostic is the sole expected signal.
// @ts-expect-error
export const missingError: Effect.Effect<User, never, UserFieldPolicy> =
  email.replace("new@example.test", source)
