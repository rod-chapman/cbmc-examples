# PQC - Post-Quantum Cryptography Examples

## Modular multiplication mod 3329

The functions in `crypto.c` show different implementations of
`(a * b) mod 3329` from the core of the Kuber/MLKEM
algorithm.

Each implemenation shows increasing contractual strength for type-safety.

See https://github.com/awslabs/LibMLKEM/blob/4e7c54f9533b00aef60a850274697a70f1078964/spark_ada/src/mlkem.adb#L121
for a full proof of partial correctness.
