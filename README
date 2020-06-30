
# What is this?

I wrote an MS thesis: "Formally Verified Space-Safety for Program Transformations".
This is that formalization, including the complete heap model and minor clean-up.

# Dependencies

This has been tested with Coq version 8.9.1
and Coq-std++ version 1.2.1

The supplied default.nix file will pick working versions of these two dependencies.

# Building

This project uses a standard coq makefile. `make all` will build everything up through the Globalization proof

# File organization

LocalTactics has tactic definitions
IO, DecEq, Steps, and SyntaxParams provide some simple ground definitions

The language and basic definitions are provided in SXML.v (this language is based mildly on the internal representation in MLton which is pre-closure conversion, but this never really panned out to much accuracy).

HeapParams defines the interesting properties of the heap and consequences.
MapHeap defines a model for this interface (which is relatively involved due to the heap closure operation)

Globalize provides the definitions for the operation and proofs of the main theorems.

Good luck
