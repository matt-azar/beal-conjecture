# Independent eclib replay of the square-summand exclusion at 2471

Task C1 verifies the operators in [the square-summand argument](../square-summand-2471.md). The C++ replay starts with eclib's full relative modular symbols at level 79072. Its inputs are the level, residual prime 31 and the first-stage trace sets. Both the basis and all fourteen Hecke matrices are constructed independently of the stored Manin-symbol matrices.

| Filter prime | Plus dimension | Minus dimension | Total |
|---:|---:|---:|---:|
| Ambient | 11336 | 11321 | 22657 |
| 3 | 112 | 97 | 209 |
| 5 | 63 | 48 | 111 |
| 11 | 44 | 29 | 73 |
| 13 | 44 | 29 | 73 |
| 17 | 21 | 21 | 42 |
| Remaining filters through 227 | 21 | 21 | 42 |

Since 2 is invertible modulo 31, the two signs recover the full space. Both eclib bases have denominator one. For each sign the program takes the direct sum of the three ordinary eigenspaces for $T_3$ at $0,4,-4$. This equals the kernel of the filter polynomial because its roots are distinct. It then constructs each small-prime operator on the successive kernels. Commutativity makes each kernel stable. Once the rows of the current basis are in reduced row echelon form, evaluating the image at the pivot columns determines all its coordinates. For these evaluations eclib applies the double cosets to primal modular symbols. The transpose acts on the dual. At the end the two sign blocks are exported in the format of the existing class verifier.

The first stage was reconstructed separately with the signed and unsigned generic trace lists. On both outputs the verifier recovers the level-32 CM control with dimension eight and checks all fourteen operators against point counts. At 61, 683 and 1117 the numbers of newly eliminated classes are 403, 512 and 46. All 961 classes are excluded. This computation uses the published level-lowering and descent inputs of the mathematical argument.

## Reproduce

The recorded run used Debian 13 amd64, GCC 14.2.0, eclib 20250122-2, FFLAS-FFPACK 2.5.0-3, Givaro 4.2.1-1, NTL 11.5.1-1+b3, GMP 6.3.0, OpenBLAS pthread 0.3.29+ds-3 and Python 3.12.14. The largest dense array has $11336^2$ single-precision entries. FFLAS-FFPACK performs finite-field linear algebra modulo 31.

```sh
c++ -O3 -std=c++17 scripts/check_square_2471_eclib.cpp -o /tmp/eclib-square \
    -lec -lntl -lgivaro -lgmpxx -lgmp -lopenblas
export OPENBLAS_NUM_THREADS=3
python scripts/check_square_2471.py filters > /tmp/square-signed.txt
/tmp/eclib-square /tmp/square-signed.txt /tmp/eclib-signed
python scripts/check_square_2471.py verify /tmp/eclib-signed
python scripts/check_square_2471.py filters --unsigned > /tmp/square-unsigned.txt
/tmp/eclib-square /tmp/square-unsigned.txt /tmp/eclib-unsigned
python scripts/check_square_2471.py verify /tmp/eclib-unsigned
```

[Replay source](../../scripts/check_square_2471_eclib.cpp) · [Full output for both runs](square-2471-eclib-output.txt)
