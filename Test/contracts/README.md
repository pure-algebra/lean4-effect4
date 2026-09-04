# Contract packets

Every semantic implementation slice begins with a breaker-authored packet in
this directory. A packet states its algebraic laws, preconditions,
postconditions, decrease arguments, frame, executable falsifiers, and the
counterexample rows it exercises. The breaker commits the packet and red
battery before the builder changes the implementation.
