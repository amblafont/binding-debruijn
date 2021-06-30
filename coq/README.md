# Initial semantics for De Bruijn monads in coq

Compilation: make

## Dependencies

Coq is required (tested with version Coq 8.12)


## Summary 

A detailed summary is available at [`Summary.v`](Summary.v).

## Axioms

Axioms are only required to construct the syntax with equations.
No axiom is used to prove initiality for the standard binding signatures.

The formalization relies on an axiomatisation of quotient types in [`Quot.v`](Quot.v)
adapted from http://web.math.unifi.it/users/maggesi/mechanized/lambda/.
It involves function extensionality.


## Files

By order of dependency:

1. [`Lib.v`](Lib.v): definition of a variant of fixed-size vectors
2. [`syntaxdb.v`](syntaxdb.v): construction of the syntax for a binding signature, with
associated proof of initiality
3. [`Quot.v`](Quot.v): axiomatization of quotient types, and various proofs about them
4. [`quotsyntax.v`](quotsyntax.v): construction of the syntax for an equational theory,
with associated proof of initiality.



