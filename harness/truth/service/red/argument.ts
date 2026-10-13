// Red control of the consumer: `add` takes a title, so a number is refused.
import { withTodo } from "../consumer.ts"

export const wrongArgument = withTodo(todo => todo.add(1))
