/**
 * The runner, wearing the everyday register.
 *
 * ## Why this module exists
 *
 * Every refusal a VERB raises already reads in house words: the
 * `userFacing` fold in `commands.ts` turns it into a `CliError.UserError`,
 * and the runner prints that alone — no help document (`Command.ts:2699`,
 * `showUserError`). The audit's grade-D rows were the refusals raised
 * BEFORE a verb runs, by the runner's own parser, which arrive as
 * `CliError.ShowHelp` and are printed as a twenty-line help dump with
 * the one useful sentence at the bottom.
 *
 * Two things are done about that, in this order.
 *
 * FIRST, and mostly: judgment was moved out of the parser. A tag byte
 * and a file that must exist are the ESTATE's laws, not the shape of an
 * argument vector, so `commands.ts` takes a plain integer and a plain
 * string and rules on them inside the handler — where `userFacing`
 * already answers at grade A. That is not a workaround; it is the
 * correct seam, and it is what removes the help dump from every row of
 * the audit's transcript.
 *
 * SECOND, for what genuinely remains — a flag that does not exist, a
 * missing argument, a misspelled verb — this module answers in the same
 * register. The runner offers no hook for it: `showHelp`
 * (`Command.ts:2684-2696`) writes the help document with an
 * UNCONDITIONAL `Console.log`, and `renderErrors: false` suppresses
 * only the error block beneath it, so catching `ShowHelp` downstream of
 * `Command.run` is too late — the dump is already on stdout. The one
 * seam that reaches that line is `CliOutput.Formatter`, which
 * `showHelp` resolves from the context.
 *
 * So the formatter here DEFERS instead of printing: it keeps the
 * document and returns nothing, and this module decides afterwards what
 * the invocation deserved. A `ShowHelp` carrying no errors is help that
 * was asked for — `cas --help`, or `cas` with no verb — and the held
 * document is printed in full. A `ShowHelp` carrying errors is a
 * refusal, and it gets the clause, the guidance, and the one usage line
 * that is actually relevant.
 */
import { Console, Effect, Option, Runtime } from "effect"
import { CliError, CliOutput, Command } from "effect/unstable/cli"
import type { HelpDoc } from "effect/unstable/cli"

/** The verbs a parent command offers, flattened out of the help
 * document's groups — what a misspelled verb is answered with. */
const verbsOf = (doc: HelpDoc.HelpDoc): ReadonlyArray<string> =>
  (doc.subcommands ?? []).flatMap((group) => group.commands.map((command) => command.name))

/** The flags a command takes, spelled as a reader would type them. The
 * runner's own globals are left out: a reader who mistyped `--store`
 * needs this verb's flags, not `--completions`. */
const flagsOf = (doc: HelpDoc.HelpDoc): ReadonlyArray<string> =>
  doc.flags.map((flag) => `--${flag.name}`)

/** A list, in prose, with no trailing punctuation to fight the line
 * it sits in. */
const listed = (items: ReadonlyArray<string>): string => items.join(", ")

/**
 * One parser refusal in the everyday register: the clause first, then
 * what would have been right. The runner's own message is used verbatim
 * only where it is already a plain sentence and there is nothing this
 * estate can add — never as a substitute for saying the fix.
 */
const refusalLines = (
  error: CliError.NonShowHelpErrors,
  doc: HelpDoc.HelpDoc,
): ReadonlyArray<string> => {
  switch (error._tag) {
    case "UnrecognizedOption": {
      const known = flagsOf(doc)
      return [
        `no such flag: ${error.option}`,
        known.length === 0
          ? `${doc.usage.split(" ")[0] ?? "this verb"} takes no flags of its own`
          : `this verb takes: ${listed(known)}`,
        ...(error.suggestions.length > 0 ? [`did you mean ${listed(error.suggestions)}?`] : []),
      ]
    }
    case "UnknownSubcommand": {
      const verbs = verbsOf(doc)
      return [
        `no such verb: ${error.subcommand}`,
        ...(verbs.length > 0 ? [`the verbs are: ${listed(verbs)}`] : []),
        ...(error.suggestions.length > 0 ? [`did you mean ${listed(error.suggestions)}?`] : []),
      ]
    }
    case "MissingArgument":
      return [
        `missing ${error.argument}`,
        ...(doc.args ?? []).filter((arg) => arg.name === error.argument).flatMap((arg) =>
          Option.match(arg.description, { onNone: () => [], onSome: (text) => [text] })
        ),
      ]
    case "MissingOption":
      return [`missing the ${error.option} flag`]
    case "UnexpectedArgument":
      return [
        `too many arguments: ${listed(error.arguments)}`,
        "this verb takes the ones its usage line names, and no more",
      ]
    case "InvalidValue":
      return [
        `${error.kind === "flag" ? error.option : `<${error.option}>`} will not take "${error.value}"`,
        error.expected,
      ]
    case "DuplicateOption":
    case "UserError":
      // A `UserError` reaching here was raised during parsing rather
      // than by a verb, and its message is already this estate's own.
      return error.message.split("\n")
    }
}

/**
 * The one parse mistake the runner cannot even see straight: a flag
 * VALUE that begins with a dash. `--kind-tag -1` is tokenized as an
 * empty `--kind-tag` plus an unknown flag `-1`, so the reader gets two
 * complaints about a mistake they did not make. Where that shape is
 * present it is collapsed to the one sentence that helps: the `=`
 * spelling.
 *
 * Three things decide which errors that is, and each is load-bearing.
 *
 * ADJACENCY. The errors arrive in argument order, so the emptied flag
 * and the token read as a flag are one mistake only when they sit next
 * to each other. An emptied flag at one end of the vector and an
 * unrecognized dashed token at the other are two mistakes, and saying
 * `--store=-1` about them would be a confident sentence about something
 * that did not happen.
 *
 * THE DASH, NOT THE DIGIT. A negative number was the case found first,
 * but nothing about the tokenizer is numeric: `--store -x` is split the
 * same way `--kind-tag -1` is, and a predicate that recognized only
 * digits answered the rest at the grade this module exists to retire.
 *
 * THE RUN, because a single-dash token is SHORT FLAGS. The runner reads
 * `-backup` as `-b -a -c -k -u -p` — six errors from one token — so the
 * value a reader typed is genuinely not recoverable from what reaches
 * here. The whole run is consumed either way, because six "no such
 * flag" lines about one typo is the riddle this collapse exists to
 * remove; but the exact `=` spelling is only printed when the run is
 * ONE token and therefore is the value. Longer than that, the sentence
 * states the rule and stops, rather than advising `--store=-b` about a
 * word the reader never typed.
 */
interface DashedValue {
  /** Where the collapse starts, and how many errors it consumes — so
   * every error that is NOT part of it is still rendered. */
  readonly at: number
  readonly through: number
  readonly lines: ReadonlyArray<string>
}

/** A flag the parser found no value for. */
const emptiedOption = (
  error: CliError.NonShowHelpErrors,
): string | undefined =>
  error._tag === "InvalidValue" && error.kind === "flag" && error.value === ""
    ? error.option
    : undefined

/** A single-dash token the parser read as a flag. `--nope` is a
 * misspelled flag and answers as one; `-b` is what a dashed VALUE is
 * broken into. */
const shortOption = (
  error: CliError.NonShowHelpErrors | undefined,
): string | undefined =>
  error !== undefined && error._tag === "UnrecognizedOption"
      && /^-[^-]/u.test(error.option)
    ? error.option
    : undefined

const dashedValuePair = (
  errors: ReadonlyArray<CliError.NonShowHelpErrors>,
): DashedValue | undefined => {
  for (const [index, error] of errors.entries()) {
    const emptied = emptiedOption(error)
    if (emptied === undefined || shortOption(errors[index + 1]) === undefined) continue
    let through = index + 1
    while (shortOption(errors[through + 1]) !== undefined) through += 1
    const only = through === index + 1 ? shortOption(errors[through]) : undefined
    return {
      at: index,
      through,
      lines: only === undefined
        ? [
          `${emptied} was left empty, and what followed it was read as flags`,
          `a value that starts with "-" is read as short flags unless the = spelling is used: --${emptied}=<value>`,
        ]
        : [
          `${emptied} was left empty, and ${only} was read as a flag`,
          `a value that starts with "-" needs the = spelling: --${emptied}=${only}`,
        ],
    }
  }
  return undefined
}

/** The refusal as the runner's formatter would have laid it out — the
 * same ERROR heading and two-space indent every other refusal in this
 * CLI already uses, so the register does not change with the source of
 * the complaint. The blank line above it is the one the runner has
 * already written by the time this is rendered.
 *
 * The dashed-value collapse REPLACES its own run and nothing else.
 * Collapsing the whole list to that one sentence was a second lie in
 * the same breath as the fix: a misspelled flag typed beside a dashed
 * value is still a misspelled flag, and dropping it means the reader
 * corrects the `=` spelling and is told about the next mistake only on
 * the next run. */
const renderRefusal = (
  errors: ReadonlyArray<CliError.NonShowHelpErrors>,
  doc: HelpDoc.HelpDoc,
): string => {
  const dashed = dashedValuePair(errors)
  const lines = dashed === undefined
    ? errors.flatMap((error) => refusalLines(error, doc))
    : errors.flatMap((error, index) =>
      index === dashed.at
        ? dashed.lines
        : index > dashed.at && index <= dashed.through
        ? []
        : refusalLines(error, doc)
    )
  return [...lines, `usage: ${doc.usage}`].map((line) => `  ${line}`).join("\n")
}

/**
 * A refusal, written and then marked as written.
 *
 * `renderErrors: false` is what keeps the runner from writing the error
 * block under the help document it was not supposed to print — but the
 * same switch also turns off its rendering of `UserError`
 * (`Command.ts:3102-3108`), which is the good path every verb here
 * already takes. So it is done here instead, in the runner's own two
 * steps: write the message, then mark it reported, so the runtime does
 * not print it a second time as an unhandled failure.
 *
 * `leadIn` is the blank line that separates a refusal from the command
 * above it, and it is a parameter because who owes it differs: on the
 * `UserError` path nothing has been written yet, and on the `ShowHelp`
 * path the runner has already written one.
 */
const showRefusal = (
  message: string,
  error: CliError.CliError,
  leadIn: string,
): Effect.Effect<void> =>
  Console.error(`${leadIn}ERROR\n${message}`).pipe(
    // `Reflect.set` rather than a cast: the property is the runtime's
    // own symbol on a value this module does not otherwise shape.
    Effect.andThen(Effect.sync(() => Reflect.set(error, Runtime.errorReported, false))),
  )

/**
 * Run the command tree over an argument vector, answering every
 * refusal in the everyday register.
 *
 * The held document is a local `let` rather than a `Ref` on purpose:
 * `CliOutput.Formatter` is a record of SYNCHRONOUS functions, so there
 * is no effect to run inside it, and the cell lives and dies inside one
 * invocation of this function.
 *
 * ## Stream discipline
 *
 * The deferring formatter answers the runner's `Console.log` with an
 * empty string, and without countermeasures that call still lands: one
 * bare newline on STDOUT, at the top of `--help` and — worse — on
 * every parse refusal, where stdout is supposed to stay empty so a
 * pipe reading it sees nothing. So the runner is given a Console whose
 * `log` swallows exactly that one write: the formatter arms a one-shot
 * flag when it defers, and the very next empty `log` is dropped. The
 * flag is one-shot and the two `formatHelpDoc` call sites in the
 * runner (`Command.ts` `showHelp`, `GlobalFlag.ts` `--help`) both log
 * immediately after formatting, so a verb's own deliberate blank line
 * — `doctor` prints one — can never be the write that is swallowed.
 * Everything else (`error`, verb output, `--version`) passes through
 * the Console that was already in context, untouched.
 */
export const runCas = <Name extends string, Input, E, R, ContextInput>(
  command: Command.Command<Name, Input, ContextInput, E, R>,
  options: { readonly version: string },
) =>
(args: ReadonlyArray<string>) => {
  let held: HelpDoc.HelpDoc | undefined
  let swallowEmptyLog = false
  const base = CliOutput.defaultFormatter()
  const deferring: CliOutput.Formatter = {
    ...base,
    formatHelpDoc: (doc) => {
      held = doc
      swallowEmptyLog = true
      return ""
    },
  }
  /** The Console in context, with the formatter's one empty write
   * dropped. Built over whatever Console the invocation already has,
   * so a capturing test Console is wrapped, never replaced. */
  const quieted = (real: Console.Console): Console.Console =>
    Object.assign(Object.create(real), {
      log: (...parts: ReadonlyArray<unknown>) => {
        if (swallowEmptyLog && parts.length === 1 && parts[0] === "") {
          swallowEmptyLog = false
          return
        }
        return real.log(...parts)
      },
    })
  /** The document the runner tried to print, printed. */
  const releaseHeld = Effect.suspend(() =>
    held === undefined ? Effect.void : Console.log(base.formatHelpDoc(held))
  )
  return Effect.flatMap(Console.Console, (real) =>
    Command.runWith(command, { ...options, renderErrors: false })(args).pipe(
      // Success with a held document is help that was asked for: the
      // `--help` flag prints through the same formatter (`GlobalFlag.ts`),
      // and it is the only thing that reaches here having stored one.
      Effect.tap(() => releaseHeld),
      Effect.tapError((error) => {
        if (!CliError.isCliError(error)) return Effect.void
        if (error._tag === "UserError") {
          // The estate's own multi-line refusals already carry the
          // two-space indent on their continuation lines, so only the
          // first needs one — exactly what the runner's formatter does.
          // Nothing has been written yet on this path, so the blank line
          // that separates a refusal from the command above it is ours.
          return showRefusal(`  ${error.userMessage ?? String(error.cause)}`, error, "\n")
        }
        if (error._tag !== "ShowHelp") return Effect.void
        // No errors beneath it means the document IS the answer: `cas`
        // with no verb, whose help is what a bare invocation should
        // print. Errors beneath it mean a refusal, and a refusal is not
        // a help request.
        if (error.errors.length === 0) return releaseHeld
        // The runner's own blank line was swallowed to keep stdout
        // empty on a refusal, so the separating newline is owed here,
        // on stderr with the rest of the message.
        return Effect.suspend(() =>
          held === undefined
            ? Effect.void
            : showRefusal(renderRefusal(error.errors, held), error, "\n")
        )
      }),
      Effect.provideService(CliOutput.Formatter, deferring),
      Effect.provideService(Console.Console, quieted(real)),
    ))
}
