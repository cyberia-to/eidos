# Binary positive arithmetic

The initial binary library uses a canonical positive inductive:
`Pos := one | bit0(Pos) | bit1(Pos)`, with meanings 1, 2n, 2n+1.
Pos has no zero constructor or leading-zero representation. It is an
unbounded positive integer, not a wrapping machine word. BNat below adds zero;
subtraction, a general reduction algorithm and machine-word refinement remain
subsequent obligations.

Successor and addition are CIC eliminator terms, with no arithmetic oracle or
new reduction rules. Host numeral construction produces O(log n) constructor
terms; all claimed arithmetic equalities are rechecked by the existing kernel.
The fixed Pos descriptor joins the strict trusted bootstrap. General user
inductives remain rejected. The representation/operation definitions, not host
Rust addition, determine the meaning of each checked equality.

Immediate application: Hemera's inverse-chain exponent decomposition and
Goldilocks modulus identities using full-width positive numerals. These are
concrete arithmetic theorems; they do not establish the field implementation.

## Nonnegative integers and reduction certificates

`BNat := zero | positive(Pos)` extends the canonical representation with zero.
Successor, addition, multiplication and strict comparison are CIC terms.
No machine-word overflow or modular reduction is implicit in these operations.

A concrete modular reduction certificate for input x and positive modulus m
contains q and r and checks both `m*q+r=x` and `r<m` through kernel reduction.
The host may propose q and r using division; its result is untrusted. Each
claim must fail if the quotient, remainder, or remainder range is wrong.
This gives concrete certificates, not a universal proof of Rust `reduce128`.
The additional fixed BNat descriptor belongs to the trusted bootstrap.

`stdlib::reduction_certificate::prove_reduction` proposes host quotient and
remainder, checks both claims, and returns their closed proof/type pairs.
`check_reduction` checks caller-provided witnesses, including deliberately
wrong ones. The interface accepts u128 inputs; the underlying multiplication
is unbounded (a product above u128::MAX must not wrap). Modulus zero is rejected.
See `examples/reduction.ei` for the surface version.

Performance limitation: substitution-based reduction remains expensive. The
dense `(2^64-1)^2` kernel test takes approximately 30 seconds in the debug build
and 8 seconds in the release test suite on the development machine. Efficient
shared reduction and resource bounds remain work; no production throughput
claim is made for this arithmetic library.
