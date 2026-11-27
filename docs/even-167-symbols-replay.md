# Modular-symbol replay for the even right base at 167

The finite sieve in [PR #36 at b5966b2](https://github.com/matt-azar/beal-conjecture/blob/b5966b2e7d407198b83395c70ba398f66951c528/scripts/check_even_base_167.gp) gives the claimed exclusions after one numerical correction. At level 334, the rational orbit has gcd 15. The PR prints 225 because PARI's generic `norm(3)` returns 9. The field norm from the rationals to themselves fixes every integer. The two gcds have the same prime divisors.

The replay uses PARI/GP 2.17.2. It calculates the Hecke operators on the plus part of the new cuspidal modular symbols and splits that space into Hecke-simple constituents. The PR computes an eigenbasis of classical modular forms. The replay obtains the absolute norms from the characteristic polynomial on each constituent. This also works when an individual eigenvalue belongs to a proper subfield. It independently counts each good fibre by summing a quadratic character, visiting every residue of the normalized square root and every odd power of the base. For the gcd it allows both multiplicative signs whenever a singular fibre exists. For the final residue tests it uses the sign of the tangent at the node and restricts the right side to actual powers.

At residual characteristic 7 a single prime of the coefficient field must pass both tests. A candidate pair outside the base field cannot match the integer traces. For a pair of residues in the base field, the eigenvalue of every combination `T3 + k*T5` must be the corresponding combination of the residues. Testing all seven characteristic polynomials leaves two candidate pairs. Each fails one of the local conditions. At level 1336, the only candidate residue of the surviving orbit at 41 is 0. At level 334 both residual-5 candidates have the wrong sign at 2.

The level-14 control comes from the solution `7 + 11^2 = 2^7`. Its unique constituent has gcd zero, and the script checks every good-prime coefficient in the specified range against a direct point count on that particular curve.

## Reproduction

Run the following command from the repository root.

```sh
gp -s 256000000 -fq scripts/check_even_167_symbols.gp </dev/null
```

Exact output follows. Rows are sorted by degree, coefficient at 2 and gcd.

```text
PARI/GP [2, 17, 2]
newspace dimensions at 2 and 8 = [0, 0]
mod 7 candidate (T3,T5) pairs = [[1, 4], [4, 6]]
admissible mod 7 at 3 and 5 = [[0, 3, 4], [0, 2, 3, 4, 5]]
level 334 sorted [degree, a2, gcd] = [[1, 1, 15], [2, -1, 1], [2, -1, 1], [2, 1, 5], [3, -1, 7168], [3, 1, 1]]
mod 5 roots of T41 = [0], admissible = [2, 3]
level 1336 sorted [degree, a2, gcd] = [[2, 0, 5], [7, 0, 1], [9, 0, 1], [12, 0, 16384], [12, 0, 65536]]
level 14 sorted [degree, a2, gcd] = [[1, -1, 0]]
```
