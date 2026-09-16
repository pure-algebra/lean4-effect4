/** The Lean-owned Forms.Template fold for every generated derived form.
 * The parsers recognize their own syntax. This module alone chooses the lowering
 * from forms.gen.ts; the two adapters construct Eff or canonical Expr nodes.
 * Re-reading an argument under inserted lexical slots is the host counterpart of
 * Forms.insert. It traverses local binders using each parser's existing reader.
 * This finite target implementation is checked against Lean-generated oracles.
 */
import { forms } from "../forms.gen.ts"
import type { ForkOptions, Lit } from "../eff.gen.ts"

type Children = "first" | "rest" | "body" | "finalizer" | "onValue" | "onCause" | "acquire" | "release"
type Subtemplates<T> = T extends object
  ? T | { [K in keyof T & Children]: Subtemplates<T[K]> }[keyof T & Children]
  : never
type WidenNumbers<T> = T extends number ? number : T extends object
  ? { readonly [K in keyof T]: WidenNumbers<T[K]> } : T
/** Derived from the generated table, including its nested argument templates. */
export type Template = WidenNumbers<Subtemplates<(typeof forms.rows)[number]["expansion"]>>
type TermTemplate = Extract<Template, { _tag: "succeed" | "die" }>["value"]

export type EffectSlot<E> = (cutOffset: number, insertions: number) => E
export interface FormArguments<E, T, K = T> {
  readonly effects: readonly EffectSlot<E>[]
  readonly terms?: readonly T[]
  readonly keys?: readonly K[]
}
export interface FormAlgebra<E, T, K = T> {
  literal(value: Lit): T
  variable(index: number): T
  succeed(value: T): E
  die(value: T): E
  bind(first: E, rest: E, depth: number): E
  onExit(body: E, finalizer: E, depth: number): E
  matchCause(body: E, onValue: E, onCause: E, depth: number): E
  service(key: K): E
  yieldNow(priority: number): E
  fork(body: E, options: ForkOptions): E
  forkIn(body: E, scope: T, options: ForkOptions): E
  forkScoped(body: E, options: ForkOptions): E
  acquireRelease(acquire: E, release: E, depth: number): E
}
export type Expansion<E> = { readonly ok: true; readonly value: E }
  | { readonly ok: false; readonly error: string }

class InvalidTemplate extends Error {}
const invalid = (message: string): never => { throw new InvalidTemplate(message) }
const natural = (value: number): number => Number.isSafeInteger(value) && value >= 0
  ? value : invalid("non-natural template index")
const slot = <T>(values: readonly T[] | undefined, index: number, kind: string): T =>
  values?.[natural(index)] ?? invalid(`missing ${kind} slot ${index}`)

/** An already-read argument is usable only where the table inserts no slots. */
export const fixedEffect = <E>(value: E): EffectSlot<E> => (_offset, count) =>
  count === 0 ? value : invalid("insertion requires an argument reader")

/** No source identifier can name the inserted NUL placeholder. Inserting before
 * a local argument binder moves that binder as well as all later positions. */
export const effectSlot = <E>(env: readonly string[], base: number,
    read: (env: readonly string[]) => E): EffectSlot<E> => (offset, count) => {
  const cut = natural(natural(base) + natural(offset))
  natural(count)
  if (cut > env.length) return invalid("insertion cut outside argument environment")
  const inner = [...env.slice(0, cut), ...Array<string>(count).fill("\u0000"), ...env.slice(cut)]
  return read(inner)
}

/** Interpret every constructor in the generated template alphabet. */
export function expandTemplate<E, T, K>(template: Template, base: number,
    args: FormArguments<E, T, K>, algebra: FormAlgebra<E, T, K>): Expansion<E> {
  try {
    natural(base)
    const term = (t: TermTemplate): T => {
      switch (t._tag) {
        case "literal": return algebra.literal(t.value)
        case "argument": return slot(args.terms, t.slot, "term")
        case "here": return algebra.variable(natural(base + natural(t.binder)))
      }
    }
    const walk = (t: Template, depth: number): E => {
      switch (t._tag) {
        case "argument": return slot(args.effects, t.slot, "effect")(
          natural(t.cutOffset), natural(t.insertions))
        case "succeed": return algebra.succeed(term(t.value))
        case "die": return algebra.die(term(t.value))
        case "bind": return algebra.bind(walk(t.first, depth), walk(t.rest, depth + 1), depth)
        case "onExit": return algebra.onExit(walk(t.body, depth), walk(t.finalizer, depth + 1), depth)
        case "matchCause": return algebra.matchCause(walk(t.body, depth),
          walk(t.onValue, depth + 1), walk(t.onCause, depth + 1), depth)
        case "service": return algebra.service(slot(args.keys, t.keySlot, "key"))
        case "yieldNow": return algebra.yieldNow(natural(t.priority))
        case "fork": return algebra.fork(walk(t.body, depth), t.options)
        case "forkIn": return algebra.forkIn(walk(t.body, depth), term(t.scope), t.options)
        case "forkScoped": return algebra.forkScoped(walk(t.body, depth), t.options)
        case "acquireRelease": return algebra.acquireRelease(walk(t.acquire, depth),
          walk(t.release, depth + 2), depth)
      }
    }
    return { ok: true, value: walk(template, base) }
  } catch (error) {
    if (error instanceof InvalidTemplate) return { ok: false, error: error.message }
    throw error // Preserve the parser's existing source refusal and unexpected failures.
  }
}

export function expandForm<E, T, K>(name: string, base: number,
    args: FormArguments<E, T, K>, algebra: FormAlgebra<E, T, K>): Expansion<E> {
  const form = forms.rows.find(row => row.id === name)
  return form ? expandTemplate(form.expansion, base, args, algebra)
    : { ok: false, error: `unknown form ${name}` }
}
