# Beal conjecture

The conjecture states that positive integers satisfying $A^x+B^y=C^z$ with $x,y,z\geq3$ have a common prime divisor in $A,B,C$. This repository investigates restrictions on a hypothetical primitive solution. The general problem remains open. [Problem statement](https://www.bealbank.com/who-we-are/our-founder/the-beal-conjecture/)

## Results

| Scope | Conclusion | Evidence |
|---|---|---|
| One summand is a square | The other summand has a prime factor at least 13. | [Published classification and verified 1,240-row filter](docs/results.md) |
| $A$ squarefree, $A^3+B^4=C^p$, $p\geq11$ prime | Either $A\equiv15\pmod{16}$ or $p$ divides the class number of $\mathbb Q(\sqrt{-A})$. | [Ideal factorization and Lucas proof](docs/results.md#the-quadratic-class-number-obstruction) |
| $167^x+b^4=c^{11}$, odd $x\geq3$ | A primitive solution requires $x\equiv1\pmod{22}$. | [Descent and finite residue calculation](docs/descent.md) |
| $2471^x+b^4=c^{31}$, odd $x\geq3$ | A primitive solution requires $x\equiv5\pmod{62}$. | [Descent and finite residue calculation](docs/descent.md) |

At $x=3$ the two fixed-base equations are impossible. The Lean files verify the finite modular contradictions in these two cases. The class-group reductions and an extension to varying bases are written proofs. The full odd-exponent sweeps have Python verifiers. [Research plan and discovery methods](docs/research-plan.md)

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

With Lean 4.19.0 (pinned by `lean-toolchain`), replay both modular certificates. They use only the Lean standard library. Each file prints the axioms of its final theorem.

```sh
lean -j1 lean/Twist167.lean
lean -j1 lean/Twist2471.lean
```
