# Independent Hecke replay at level 8416

The replay for PR #28 starts with both complex-conjugation signs of eclib's relative modular-symbol space. It rebuilds the bases, applies the generic trace filters and constructs all eleven requested Hecke matrices over the field with 13 elements. Its only shared numerical inputs with the original Hecke calculation are the level, residue characteristic, filter sets and prime lists.

| Stage | Plus | Minus | Total |
|---|---:|---:|---:|
| Ambient | 1060 | 1053 | 2113 |
| After 3 | 23 | 16 | 39 |
| After 5 | 7 | 7 | 14 |
| After 7 and through 61 | 2 | 2 | 4 |

All eleven operators are scalar on the final four-dimensional space. Direct point counts on the level-32 curve give the same eleven scalars. At 157, 313 and 521 they are 9, 0 and 4 modulo 13. Running the PR's verifier on independently generated matrices eliminates 159, 8 and 2 classes in succession, leaving zero. Allowing both multiplicative signs from the first stage gives identical output matrices.

Use eclib 20250122-2, FFLAS-FFPACK 2.5.0-3, Givaro 4.2.1-1, NTL 11.5.1-1+b3, GMP 6.3.0, OpenBLAS pthread 0.3.29+ds-3, GCC 14.2.0 and Python 3.12.14. In the commands, `r5` is a checkout containing PR #28 at `129fd45`. The two-argument form of the executable still selects 2471. The trailing argument `263` selects the new case.

```sh
c++ -O3 -std=c++17 scripts/check_square_2471_eclib.cpp -o /tmp/square-eclib \
    -lec -lntl -lgivaro -lgmpxx -lgmp -lopenblas
export OPENBLAS_NUM_THREADS=2
cd ../r5
python scripts/check_square_class_test.py --base 263 filters > /tmp/r5-signed
/tmp/square-eclib /tmp/r5-signed /tmp/e263 263
python scripts/check_square_class_test.py --base 263 verify /tmp/e263
python scripts/check_square_class_test.py --base 263 filters --unsigned > /tmp/r5-unsigned
/tmp/square-eclib /tmp/r5-unsigned /tmp/e263u 263
python scripts/check_square_class_test.py --base 263 verify /tmp/e263u
```

[Full output](square-263-eclib-output.txt) · [Hecke implementation](../../scripts/check_square_2471_eclib.cpp)
