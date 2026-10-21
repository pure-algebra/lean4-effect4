<!-- walk-view.lean (prove-out)
-->
# The to-do as graphs

| ours | Effect TypeScript | algebra |
| --- | --- | --- |
| a host namespace of rows | a Layer\<Tag\> the host supplies | a comodel of the row signature |
| a service block | Layer.effect(Tag, map(init, closures)) | a handler, one program per method |
| the main program | Effect.provide(program, layer) | a term over the methods, handled |
| rows a block calls | Layer.provide(block, host) | composition: connect(host, block) |
| two blocks of disjoint services | Layer.merge | the tensor: overlay |
| a second block of one service | a second Layer of one Tag | a second handler; the same boundary |

D1 the boundary, Mokhov's graph: boxes and dependency edges

```mermaid
flowchart TB
  n0["TodoRepo host<br/>host · reactor, state σ"]
  n1["Session host<br/>host · reactor, state σ"]
  n2["TodoApp block<br/>handler · init once, bodies"]
  n3["main program<br/>user code"]
  n0 --> n2
  n2 --> n3
  n1 --> n3
```

D1 the cached block has the same boundary

```mermaid
flowchart TB
  n0["TodoRepo host<br/>host · reactor, state σ"]
  n1["Session host<br/>host · reactor, state σ"]
  n2["ListCache block<br/>handler · init once, bodies"]
  n3["TodoApp block<br/>handler · init once, bodies"]
  n4["main program<br/>user code"]
  n0 --> n3
  n2 --> n3
  n3 --> n4
  n1 --> n4
```

D3 the boundary as a hypergraph: wires are nodes typed by a tag

```mermaid
flowchart TB
  n0["TodoRepo host<br/>host · reactor, state σ"]
  n1["Session host<br/>host · reactor, state σ"]
  n2["TodoRepo<br/>wire · a service tag"]
  n3["Session<br/>wire · a service tag"]
  n4["TodoApp block<br/>handler · init once, bodies"]
  n5["TodoApp<br/>wire · a service tag"]
  n6["main program<br/>user code"]
  n0 --> n2
  n4 --> n5
  n1 --> n3
  n2 --> n4
  n5 --> n6
  n3 --> n6
```

D2 a layer term as a term graph: provide over merge over fresh

```mermaid
flowchart TB
  n0["provide<br/>layer"]
  n1["effect<br/>layer · tag 6"]
  n2["merge<br/>layer"]
  n3["effect<br/>layer · tag 4"]
  n4["fresh<br/>layer"]
  n5["effect<br/>layer · tag 4"]
  n0 --> n1
  n0 --> n2
  n2 --> n3
  n2 --> n4
  n4 --> n5
```

G2 inside the box: the call graph of the session object, plain

```mermaid
flowchart TB
  n0["main<br/>user code"]
  n1["TodoApp_add<br/>definition"]
  n2["TodoApp_list<br/>definition"]
  n3["TodoApp_complete<br/>definition"]
  n4["TodoApp_remove<br/>definition"]
  n5["TodoAppContext<br/>definition"]
  n6["Session.next<br/>row"]
  n7["Session.reply_add<br/>row"]
  n8["Session.reply_list<br/>row"]
  n9["Session.reply_complete<br/>row"]
  n10["Session.reply_remove<br/>row"]
  n11["TodoRepo.insert<br/>row"]
  n12["TodoRepo.all<br/>row"]
  n13["TodoRepo.setDone<br/>row"]
  n14["TodoRepo.delete<br/>row"]
  n1 --> n11
  n2 --> n12
  n3 --> n13
  n4 --> n14
  n0 --> n5
  n0 --> n6
  n0 --> n1
  n0 --> n7
  n0 --> n2
  n0 --> n8
  n0 --> n3
  n0 --> n9
  n0 --> n4
  n0 --> n10
```

