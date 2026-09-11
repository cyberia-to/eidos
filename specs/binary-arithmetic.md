# Binary positive arithmetic

The initial binary library uses a canonical positive inductive:
`Pos := one | bit0(Pos) | bit1(Pos)`, with meanings 1, 2n, 2n+1.
There is no zero constructor and no leading-zero representation. This is an
unbounded positive integer, not a wrapping machine word. Zero, subtraction,
modular reduction and machine-word refinement are subsequent obligations.

Successor and addition are CIC eliminator terms, with no arithmetic oracle or
new reduction rules. Host numeral construction produces O(log n) constructor
terms; all claimed arithmetic equalities are rechecked by the existing kernel.
The fixed Pos descriptor joins the strict trusted bootstrap. General user
inductives remain rejected. The representation/operation definitions, not host
Rust addition, determine the meaning of each checked equality.

Immediate application: Hemera's inverse-chain exponent decomposition and
Goldilocks modulus identities using full-width positive numerals. These are
concrete arithmetic theorems; they do not establish the field implementation.
