# Beal conjecture

The conjecture states that positive integers satisfying $A^x+B^y=C^z$ with $x,y,z\geq3$ have a common prime divisor in $A,B,C$. This repository investigates restrictions on a hypothetical primitive solution. The general problem remains open. [Problem statement](https://www.bealbank.com/who-we-are/our-founder/the-beal-conjecture/)

## Results

**For $A\in\{167,263,2471\}$, there is no positive primitive solution of $A^x+B^y=C^z$ whenever $4\mid y$ and $x,y,z\geq3$.** The proof covers unbounded bases $B,C$ and unbounded exponents. It combines ideal descent, the primitive-divisor theorem, published results on generalized Fermat equations, and exact modular-form calculations. Only selected descent implications have been checked in Lean. [Complete proof by cases](docs/fixed-bases.md) · [Expert collaborator guide](docs/collaborating.md)

| Other scope | Conclusion |
|---|---|
| $A=167$, even $y$ and $11\mid z$ | The stronger equation $167^x+U^2=c^{11}$ has no primitive solution for any positive $x,U,c$. [Arbitrary square summand](docs/frey-167.md#an-arbitrary-square-summand-at-exponent-11) |
| One summand is a square | The complementary summand has a prime divisor at least 13. [Proof and verified 1,240-row classification filter](docs/results.md) |
| Odd $x$, fourth-power summand, squarefree first base $A$, right exponent divisible by prime $p\geq11$ | Either $A\equiv15\pmod{16}$ or $p$ divides the class number of $\mathbb Q(\sqrt{-A})$. [Quadratic class-number obstruction](docs/results.md#the-quadratic-class-number-obstruction) |
| Right exponent divisible by 11 or 31, varying first summand | The modular arguments exclude infinite families with a free multiplier and stated local conditions. [Exponent 11](docs/frey-167.md#varying-the-first-summand) · [Exponent 31](docs/varying-base.md) |

At level 79072 the decisive Hecke determinant is $29\bmod31$. A classical modular-symbol computation independently verifies the exclusion. The two twists it rules out had points over every completion of $\mathbb Q$. At 263 a separate argument proves every affine rational point on a rank-one Mordell curve has a denominator divisible by 26723. [Rank and denominator proof](docs/transfer-263.md#a-denominator-obstruction-on-the-remaining-mordell-curve) · [Exact Hecke calculation](docs/brandt-sieve.md) · [Local points](docs/local-points.md) · [Research priorities and evidence](docs/research-plan.md)

## Reproduce the calculations

From the repository root, use Python 3.9 or later. The first command checks the class numbers, principalizing elements, cubic certificates and odd-exponent sweeps.

```sh
python3 scripts/check_twists.py --exponents
```

The cubic right-side certificates and auxiliary Frey traces run with standard Python. The Hecke replays use PARI/GP 2.17.2 and Python with `numpy==2.3.5` and `python-flint==0.9.0`, respectively. The classical C++ replay and its dependencies are in the [expert guide](docs/collaborating.md#verification).

```sh
python3 scripts/check_cubic_twists.py
python3 scripts/check_aux_traces.py --base 167
python3 scripts/check_aux_traces.py --base 2471
gp -q -f scripts/check_new_5344.gp
gp -q -f scripts/check_transfer_263.gp
gp -q -f scripts/check_mordell_263.gp
python3 scripts/check_brandt.py
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
gp -fq scripts/check_trace_ideal_classes.gp
c++ -O2 -std=c++17 scripts/check_local_points.cpp -o /tmp/beal-local-points
/tmp/beal-local-points
```

Build the formal results with Lean 4.19.0, pinned by `lean-toolchain`, and Mathlib `v4.19.0` (for `IdealDescent`). Top-level theorem names and their assumptions are in the [expert guide](docs/collaborating.md).

```sh
lake exe cache get
lake build
```
