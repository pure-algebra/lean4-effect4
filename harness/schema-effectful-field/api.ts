import { Context, Effect, Optic } from "effect"

interface User {
  readonly id: string
  readonly email: string
}

type ReadEmailError = { readonly _tag: "ReadEmailError" }
type WriteEmailError = { readonly _tag: "WriteEmailError" }

class UserFieldPolicy extends Context.Service<UserFieldPolicy, {
  readonly readEmail: (source: User) => Effect.Effect<string, ReadEmailError>
  readonly writeEmail: (
    source: User,
    value: string
  ) => Effect.Effect<void, WriteEmailError>
}>()("UserFieldPolicy") {}

const emailLens = Optic.id<User>().key("email")

export const email = {
  get: (source: User): Effect.Effect<string, ReadEmailError, UserFieldPolicy> =>
    Effect.gen(function*() {
      const service = yield* UserFieldPolicy
      return yield* service.readEmail(source)
    }),

  replace: (
    value: string,
    source: User
  ): Effect.Effect<User, WriteEmailError, UserFieldPolicy> =>
    Effect.gen(function*() {
      const service = yield* UserFieldPolicy
      yield* service.writeEmail(source, value)
      return emailLens.replace(value, source)
    }),

  modify: (
    f: (value: string) => string,
    source: User
  ): Effect.Effect<
    User,
    ReadEmailError | WriteEmailError,
    UserFieldPolicy
  > => Effect.flatMap(email.get(source), (value) => email.replace(f(value), source))
} as const

const source: User = { id: "user-1", email: "old@example.test" }
