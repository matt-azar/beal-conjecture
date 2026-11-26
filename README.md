# Beal conjecture

The conjecture states that positive integers satisfying $A^x+B^y=C^z$ with $x,y,z\geq3$ have a common prime divisor in $A,B,C$. This repository investigates restrictions on a hypothetical primitive solution. The general problem remains open. [Problem statement](https://www.bealbank.com/who-we-are/our-founder/the-beal-conjecture/)

The [expert guide](docs/collaborating.md) gives the precise open equation, computations to replay, conventions for combining independent work, and remaining proof obligations.

## Results

| Scope | Conclusion | Evidence |
|---|---|---|
| One summand is a square | The other summand has a prime factor at least 13. | [Published classification and verified 1,240-row filter](docs/results.md) |
| $A$ squarefree, $A^3+B^4=C^p$, $p\geq11$ prime | Either $A\equiv15\pmod{16}$ or $p$ divides the class number of $\mathbb Q(\sqrt{-A})$. | [Ideal factorization and Lucas proof](docs/results.md#the-quadratic-class-number-obstruction) |
| $167^x+b^4=c^{11}$, odd $x\geq3$ | A primitive solution requires $x\equiv1\pmod{22}$. | [Descent and finite residue calculation](docs/descent.md) |
| $2471^x+b^4=c^{31}$, odd $x\geq3$ | A primitive solution requires $x\equiv5\pmod{62}$. | [Descent and finite residue calculation](docs/descent.md) |

**The remaining case at 31.** Every primitive solution with $d=2471$ would satisfy $683\mid c$. Each surviving twist has primitive points over every completion of $\mathbb Q$. A global descent expresses both survivors using one irreducible Thue–Mahler form of degree 31. Its primitive solutions subject to the square and valuation constraints remain to be determined. [Local points](docs/local-points.md) · [Global reduction](docs/thue-mahler.md) · [Number-field inputs](docs/trace-field.md) · [Frey curve and remaining newforms](docs/frey-curve.md)

At $x=3$ both fixed-base equations are impossible. Lean checks the implications from a shared integral twist identity to contradiction for both bases. Deriving the identity from the class group is still a written proof. The odd-exponent sweeps use Python. [Research plan](docs/research-plan.md)

## Reproduce the calculations

From the repository root, use Python 3.9 or later. The first command checks the class numbers, principalizing elements, cubic certificates and odd-exponent sweeps.

```sh
python3 scripts/check_twists.py --exponents
```

For the smooth-summand result, obtain the authors' table at the pinned revision. The verifier authenticates the file by SHA-256 and checks each row's arithmetic.

```sh
git clone https://github.com/samirsiksek/lebnag.git ../lebnag
git -C ../lebnag show e8b1dab1f30487b0c38eee94b297bd88c821924f:lebesgue_nagell_solutions.txt > ../lebesgue_nagell_solutions.txt
python3 scripts/check_smooth.py ../lebesgue_nagell_solutions.txt
```

To reproduce the exponent-31 global and local computations, run the following commands. The GP script uses PARI/GP (tested with 2.17.2). The C++ verifier checks all exceptional and small good primes in the local argument.

```sh
python3 scripts/check_residual_form.py
gp -fq scripts/check_trace_field.gp
c++ -O2 -std=c++17 scripts/check_local_points.cpp -o /tmp/beal-local-points
/tmp/beal-local-points
```

Build the formal results with Lean 4.19.0, pinned by `lean-toolchain`, and Mathlib `v4.19.0` (for `IdealDescent`). Top-level theorem names and their assumptions are in the [expert guide](docs/collaborating.md).

```sh
lake exe cache get
lake build
```
