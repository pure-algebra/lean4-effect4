// Seat T fixture for T.moduleTypeRef; counts in module-types.expected.tsv.
import type { Duration, Option, Queue, Stream } from "effect"
type S = Stream.Stream<number>
type Q = Queue.Dequeue<{ readonly id: number }>
type D = Duration.Duration
type O = Option.Option<string>
