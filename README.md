# automata

This is a general-purpose library for working with several different types
of automata. This library provides:

* Deterministic Finite-State Automata (DFSA): variants in which the input
  token is boxed or is unboxed. When possible, convert to the variant that
  uses unboxed input before evaluating.
* Nondeterministic Finite-State Automata (NFSA)
* Deterministic Finite-State Transducers (DFST): variants in which the input
  is boxed or unboxed. Also includes a read-only run-length-encoded variant
  that helps performance when the grammar described includes long static
  runs of characters.
* Nondeterministic Finite-State Transducers (NFST)

The internal representations of automata and transducers provided by this
library are optimized for evaluating input. This library prioritizes high
performance of input evaluation over performance in any other area.

Functions for combining automata are correct and are within a constant factor
of the best known algorithms. However, this constant factor may be ten or a
hundred times higher than it could be. I'm not sure since I have not actually
measured these implementations against a good implementation in C. If anyone
has the need and the desire to improve performance in this area (and there is
certainly some low-hanging fruit here), PRs are welcome. There are already
benchmarks in place to measure performance of DFSA union.
