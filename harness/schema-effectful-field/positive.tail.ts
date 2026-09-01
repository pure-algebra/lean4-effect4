type Equal<A, B> =
  (<T>() => T extends A ? 1 : 2) extends
    (<T>() => T extends B ? 1 : 2) ? true : false
type Assert<T extends true> = T

type _GetSuccess = Assert<Equal<
  Effect.Success<ReturnType<typeof email.get>>,
  string
>>
type _GetError = Assert<Equal<
  Effect.Error<ReturnType<typeof email.get>>,
  ReadEmailError
>>
type _GetServices = Assert<Equal<
  Effect.Services<ReturnType<typeof email.get>>,
  UserFieldPolicy
>>
type _ReplaceSuccess = Assert<Equal<
  Effect.Success<ReturnType<typeof email.replace>>,
  User
>>
type _ReplaceError = Assert<Equal<
  Effect.Error<ReturnType<typeof email.replace>>,
  WriteEmailError
>>
type _ReplaceServices = Assert<Equal<
  Effect.Services<ReturnType<typeof email.replace>>,
  UserFieldPolicy
>>
type _ModifyError = Assert<Equal<
  Effect.Error<ReturnType<typeof email.modify>>,
  ReadEmailError | WriteEmailError
>>
type _ModifyServices = Assert<Equal<
  Effect.Services<ReturnType<typeof email.modify>>,
  UserFieldPolicy
>>

const events: Array<string> = []
const live: UserFieldPolicy["Service"] = {
  readEmail: (value) => Effect.sync(() => {
    events.push(`read:${value.email}`)
    return "fresh@example.test"
  }),
  writeEmail: (_source, value) => Effect.sync(() => {
    events.push(`write:${value}`)
  })
}

const changed = await Effect.runPromise(
  email.modify((value) => value.toUpperCase(), source).pipe(
    Effect.provideService(UserFieldPolicy, live)
  )
)

if (changed.email !== "FRESH@EXAMPLE.TEST") {
  throw new Error(`effectful field returned ${changed.email}`)
}
if (events.join("|") !==
    "read:old@example.test|write:FRESH@EXAMPLE.TEST") {
  throw new Error(`effectful field order was ${events.join("|")}`)
}

console.log("schema effectful field: directional types and read/write order passed")
