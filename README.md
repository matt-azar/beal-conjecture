# Beal conjecture

The conjecture states that positive integers satisfying $A^x+B^y=C^z$ with $x,y,z\geq3$ have a common prime divisor in $A,B,C$. This repository investigates restrictions on a hypothetical primitive solution. The general problem remains open. [Problem statement](https://www.bealbank.com/who-we-are/our-founder/the-beal-conjecture/)

## Results

**For $A\in\{167,263,2471\}$, there is no positive primitive solution of $A^x+B^y=C^z$ whenever $4\mid y$ and $x,y,z\geq3$.** The proof covers unbounded bases $B,C$ and unbounded exponents. It combines ideal descent, the primitive-divisor theorem, published results on generalized Fermat equations, and exact modular-form calculations. Only selected descent implications have been checked in Lean. [Complete proof by cases](docs/fixed-bases.md) · [Expert collaborator guide](docs/collaborating.md)

**Status.** These results are claimed, not established. None has had external review. Within the project, the theorem statements cited in the fixed-base proof have been compared with their sources, and the numerical and Lean replays have been reproduced from clean checkouts. The mathematical [audit](docs/audit.md) has so far covered only the elementary skeleton of the fixed-base proof. The modular exclusions, the cubic cases and the argument at 263 are not yet audited. [Clean replay](docs/clean-replay.md)

**What is new.** The method is not new. Bennett and Siksek solved $X^2+q^\alpha=y^n$ for every prime $q<100$, and for even $\alpha$ for every prime $q<1000$, by the same combination of primitive divisors and Frey curves. Their even-exponent theorem already contains the cases of the result above with $x$ even at 167 and 263. The cases with $x$ odd are the ones not found in the literature. They lie where the classical arguments stop: $d\equiv7\pmod 8$, an even square, and a right exponent dividing the class number. [Prime power gaps, Theorems 1 and 4](https://arxiv.org/abs/2110.05553) · [Literature survey](docs/literature-survey.md)

| Other scope | Conclusion |
|---|---|
| $A=167$, even $y$ and $11\mid z$ | The stronger equation $167^x+U^2=c^{11}$ has no primitive solution for any positive $x,U,c$. [Arbitrary square summand](docs/frey-167.md#an-arbitrary-square-summand-at-exponent-11) |
| $A=2471$, even $y$ and $31\mid z$ | The stronger equation $2471^x+U^2=c^{31}$ has no primitive solution for any positive $x,U,c$. This includes $2471^x+B^6=C^{31}$. Not yet reviewed, and its Hecke computation has one implementation so far. [Arbitrary square summand](docs/square-summand-2471.md) |
| One summand is a square | The complementary summand has a prime divisor at least 13. [Proof and verified 1,240-row classification filter](docs/results.md) |
| Odd $x$, fourth-power summand, squarefree first base $A$, right exponent divisible by prime $p\geq11$ | Either $A\equiv15\pmod{16}$ or $p$ divides the class number of $\mathbb Q(\sqrt{-A})$. [Quadratic class-number obstruction](docs/results.md#the-quadratic-class-number-obstruction) |
| Right exponent divisible by 11 or 31, varying first summand | The modular arguments exclude infinite families with a free multiplier and stated local conditions. [Exponent 11](docs/frey-167.md#varying-the-first-summand) · [Exponent 31](docs/varying-base.md) |

At level 79072 the decisive Hecke determinant is $29\bmod31$. A classical modular-symbol computation independently verifies the exclusion. The two twists it rules out had points over every completion of $\mathbb Q$. At 263 a separate argument proves every affine rational point on a rank-one Mordell curve has a denominator divisible by 26723. [Rank and denominator proof](docs/transfer-263.md#a-denominator-obstruction-on-the-remaining-mordell-curve) · [Exact Hecke calculation](docs/brandt-sieve.md) · [Local points](docs/local-points.md) · [Research priorities and evidence](docs/research-plan.md)

## Reproduce the calculations

From the repository root, use Python 3.9 or later. The first command checks the class numbers, principalizing elements, cubic certificates and odd-exponent sweeps.

```sh
python3 scripts/check_twists.py --exponents
```

The cubic right-side certificates and auxiliary Frey traces use standard Python. The modular calculations use PARI/GP 2.17.2 or Python with `numpy==2.3.5` and `python-flint==0.9.0`. The standalone C++ modular-symbol replay requires AVX2 and OpenMP. It reaches the level-79072 exclusion without the trace at 683. [Standalone commands and expected output](docs/modular-symbols-replay.md) · [Classical eclib dependencies](docs/collaborating.md#verification) · [Clean replay with pinned versions](docs/clean-replay.md)

```sh
python3 scripts/check_cubic_twists.py
python3 scripts/check_aux_traces.py --base 167
python3 scripts/check_aux_traces.py --base 2471
gp -q -f scripts/check_new_5344.gp
gp -q -f scripts/check_transfer_263.gp
gp -q -f scripts/check_mordell_263.gp
python3 scripts/check_brandt.py
python3 scripts/audit_skeleton.py
```

For the smooth-summand result, obtain the authors' table at the pinned revision. The verifier authenticates the file by SHA-256 and checks each row's arithmetic.

```sh
git clone https://github.com/samirsiksek/lebnag.git ../lebnag
git -C ../lebnag show e8b1dab1f30487b0c38eee94b297bd88c821924f:lebesgue_nagell_solutions.txt > ../lebesgue_nagell_solutions.txt
python3 scripts/check_smooth.py ../lebesgue_nagell_solutions.txt
```

The arbitrary-square result at 2471 has its own replay. The command below checks all 961 descent classes against stored Hecke matrices in under a minute. Regenerating the matrices takes about ten minutes with the C++ program. [Commands and expected output](docs/square-summand-2471.md#reproduction)

```sh
python3 scripts/check_square_2471.py verify
```

To reproduce the exponent-31 global and local computations, run the following commands. The GP script uses PARI/GP (tested with 2.17.2). The C++ verifier checks all exceptional and small good primes in the local argument.

```sh
python3 scripts/check_residual_form.py
gp -fq scripts/check_trace_field.gp
gp -fq scripts/check_trace_ideal_classes.gp
c++ -O2 -std=c++17 scripts/check_local_points.cpp -o /tmp/beal-local-points
/tmp/beal-local-points
```

Build with Lean 4.19.0 and Mathlib v4.19.0. For $d=167,2471$, Lean realizes `IdealAPI` using Mathlib ideals of $\mathbb Z[\omega]$, with $\omega=(1+\sqrt{-d})/2$. The exclusions for left exponent $x=3$ at right exponents 11 and 31, respectively, still assume `DedekindGap`. [Concrete ideal implementation](lean/OmegaRing.lean) · [Theorems and assumptions](docs/collaborating.md#verification)

```sh
lake exe cache get
lake build
```
