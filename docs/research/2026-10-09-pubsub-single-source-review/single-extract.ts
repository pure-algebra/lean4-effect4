class BoundedPubSubSingle<in out A> implements PubSub.Atomic<A> {
  publisherIndex = 0
  subscriberCount = 0
  subscribers = 0
  value: A = AbsentValue as unknown as A
  replayIndex = 0

  readonly capacity = 1
  readonly replayBuffer: ReplayBuffer<A> | undefined

  constructor(replayBuffer: ReplayBuffer<A> | undefined) {
    this.replayBuffer = replayBuffer
  }

  replayWindow(): PubSub.ReplayWindow<A> {
    return this.replayBuffer ? new ReplayWindowImpl(this.replayBuffer) : emptyReplayWindow
  }

  pipe() {
    return pipeArguments(this, arguments)
  }

  isEmpty(): boolean {
    return this.subscribers === 0
  }

  isFull(): boolean {
    return !this.isEmpty()
  }

  size(): number {
    return this.isEmpty() ? 0 : 1
  }

  publish(value: A): boolean {
    if (this.isFull()) {
      return false
    }
    const replayIndex = this.replayBuffer?.offer(value)
    if (this.subscriberCount !== 0) {
      this.value = value
      if (replayIndex !== undefined) {
        this.replayIndex = replayIndex
      }
      this.subscribers = this.subscriberCount
      this.publisherIndex += 1
    }
    return true
  }

  publishAll(elements: Iterable<A>): Array<A> {
    if (this.subscriberCount === 0) {
      if (this.replayBuffer) {
        this.replayBuffer.offerAll(elements)
      }
      return []
    }
    const chunk = Arr.fromIterable(elements)
    if (chunk.length === 0) {
      return chunk
    }
    if (this.publish(chunk[0])) {
      return chunk.slice(1)
    } else {
      return chunk
    }
  }

  slide(): void {
    if (this.isFull()) {
      const value = this.value
      this.subscribers = 0
      this.value = AbsentValue as unknown as A
      this.replayBuffer?.slide(value, this.replayIndex)
    }
  }

  subscribe(): PubSub.BackingSubscription<A> {
    this.subscriberCount += 1
    return new BoundedPubSubSingleSubscription(this, this.publisherIndex, false)
  }
}

class BoundedPubSubSingleSubscription<in out A> implements PubSub.BackingSubscription<A> {
  private self: BoundedPubSubSingle<A>
  private subscriberIndex: number
  private unsubscribed: boolean

  constructor(
    self: BoundedPubSubSingle<A>,
    subscriberIndex: number,
    unsubscribed: boolean
  ) {
    this.self = self
    this.subscriberIndex = subscriberIndex
    this.unsubscribed = unsubscribed
  }

  isEmpty(): boolean {
    return (
      this.unsubscribed ||
      this.self.subscribers === 0 ||
      this.subscriberIndex === this.self.publisherIndex
    )
  }

  size() {
    return this.isEmpty() ? 0 : 1
  }

  poll(): A | MutableList.Empty {
    if (this.isEmpty()) {
      return MutableList.Empty
    }
    const elem = this.self.value
    this.self.subscribers -= 1
    if (this.self.subscribers === 0) {
      this.self.value = AbsentValue as unknown as A
    }
    this.subscriberIndex = this.self.publisherIndex
    return elem
  }

  pollUpTo(n: number): Array<A> {
    if (Count.normalize(n) < 1 || this.isEmpty()) {
      return []
    }
    return [this.poll() as A]
  }

  unsubscribe(): void {
    if (!this.unsubscribed) {
      this.unsubscribed = true
      this.self.subscriberCount -= 1
      if (this.self.subscribers !== 0 && this.subscriberIndex !== this.self.publisherIndex) {
        this.self.subscribers -= 1
        if (this.self.subscribers === 0) {
          this.self.value = AbsentValue as unknown as A
        }
      }
    }
  }
}

interface Node<out A> {
  value: A | AbsentValue
  replayIndex: number | undefined
  subscribers: number
  next: Node<A> | null
}

