# A descent that retains the ideal class

Consider a primitive equation $d^x+b^4=c^p$ with odd $x\geq3$. The bases are positive. The two cases below allow unbounded $b,c,x$. Fourth-power or $p$th-power exponents can be multiplied by any positive integer by absorbing the quotient into the base.

| Squarefree $d$ | Prime $p$ | Necessary condition on $x$ | Surviving pairs $(x\bmod 4p,k)$ |
|---:|---:|---|---|
| 167 | 11 | $x\equiv1\pmod{22}$ | $(1,4),(23,7)$ |
| 2471 | 31 | $x\equiv5\pmod{62}$ | $(5,23),(67,8)$ |

In particular, **neither $167^3+b^4=c^{11}$ nor $2471^3+b^4=c^{31}$ has a primitive solution**. The exponent restrictions above are necessary conditions. The modular arguments subsequently exclude each surviving class. [Base 167](frey-167.md) · [Base 2471](frey-curve.md)

## From an integer solution to a twist

Both $d$ are $7\pmod{16}$, and $2471=7\cdot353$ is squarefree. If $c$ were even then $b$ would be odd and $d^x+b^4\equiv8\pmod{16}$, impossible. Set $s=\sqrt{-d}$ and $R=\mathbb Z[(1+s)/2]$, the ring of integers of $K=\mathbb Q(s)$. Put $a=d^{(x-1)/2}$ and $\gamma=b^2+as$. Its norm is $c^p$. The conjugate factors generate coprime ideals since $\gcd(c,2d)=1$. Consequently $(\gamma)=I^p$ for an integral ideal $I$, and the class of $I$ belongs to $\mathrm{Cl}(K)[p]$.

| $d$ | Discriminant | Class number | $\eta$ with norm $2^p$ |
|---:|---:|---:|---|
| 167 | $-167$ | 11 | $(3+7s)/2$ |
| 2471 | $-2471$ | 62 | $(90621+391s)/2$ |

These class numbers can be verified unconditionally by listing the primitive reduced forms $[u,v,w]$ of discriminant $-d$. Enumerate $1\leq u\leq\sqrt{d/3}$, $|v|\leq u\leq w$, $w=(v^2+d)/(4u)$ integral, and require $v\geq0$ on either boundary $|v|=u$ or $u=w$. Reduced forms represent the ideal classes once each. [Reduced-form correspondence, preamble to Problem 6, p. 8](https://math.mit.edu/classes/18.785/2021fa/ProblemSet9.pdf) · [Reproduce the counts and residue tables](../scripts/check_twists.py)

Since $-d\equiv1\pmod8$, the prime 2 splits. Each displayed $\eta$ has odd trace and norm $2^p$, so its ideal is $P^p$ for one prime $P$ above 2. Indeed, divisibility by both primes would give $\eta\in2R$ and even trace. The prime $P$ is nonprincipal since a norm-two element would give $u^2+dv^2=8$, which has no integer solutions. Thus $[P]$ has order $p$. In both class numbers $p$ occurs to exponent one. It follows that $[P]$ generates $\mathrm{Cl}(K)[p]$, including in the second field where the full class group has order 62.

For a single $k\in\{0,\ldots,p-1\}$ we have $IP^k=(\beta)$ with $\beta\in R$. Raising ideals to the $p$th power and absorbing the unit $\pm1$ gives the identity

$$
\beta^p=\eta^k(b^2+as).
$$

The same $k$ must work at every modulus. This is what was lost when attempting to extract a $p$th root of $\gamma$ itself.

## The cubic certificates

For $x=3$, we have $a=d$. For each odd modulus $m$ below choose $r$ with $r^2\equiv-d\pmod m$. The two substitutions $s\mapsto r,-r$ define ring maps $R\to\mathbb Z/m\mathbb Z$ because 2 is invertible. Under both maps the identity must be a $p$th power for the **same** $b\bmod m$. The two roots of those powers may differ, and $b$ may have a different residue at another modulus. The test includes zero and nonunits, in particular at $m=p^2$.

| $d$ | $m$ | $r$ | Twist indices still possible after this row |
|---:|---:|---:|---|
| 167 | 121 | 14 | $0,1,4,6$ |
| 167 | 199 | 80 | none |
| 2471 | 961 | 90 | $1,2,6,7,8,9,12,16,19,20,22,23,29$ |
| 2471 | 683 | 332 | $19,23$ |
| 2471 | 1117 | 552 | $19$ |
| 2471 | 2791 | 1030 | none |

For example, modulo 199 alone the possible indices are $2,3,5,7,8,9,10$, disjoint from the four allowed by 121. These are exhaustive searches of *residue rings*. Bounds on the original integer bases play no role. Lean checks that simultaneous local witnesses cannot exist for either row group. The [quadratic bridge](../lean/QuadraticBridge.lean) takes an integral twist identity to these witnesses in Lean. Its ideal-theoretic premise follows from the written proof above. [Lean certificate for 167](../lean/Twist167.lean) · [Lean certificate for 2471](../lean/Twist2471.lean)

## All odd exponents for the two fixed bases

For each modulus used here $d$ is a unit. Increasing $x$ by $4p$ multiplies $a$ by $d^{2p}$. Dividing the local identity by $d^{2p}$ rescales $\beta$ by $d^{-2}$ and $b$ by $d^{-p}$. Both substitutions are invertible, so admissibility depends only on $x\bmod 4p$.

We may also discard $k=0$ for every actual odd $x\geq3$. In this branch $I$ is principal. The [Lucas argument](results.md) applies directly to $v L_p=2d^{(x-1)/2}$, even though the full class group contains $p$-torsion. Enumerating the remaining twists gives the two rows at the top of this note. Residue $x=1$ represents permissible *congruence classes* of exponents, including positive exponents larger than one.

| $d$ | Moduli used for the two substitutions |
|---:|---|
| 167 | 89, 121, 199, 353, 397 |
| 2471 | 683, 961, 1117, 1303, 1489, 2357, 2543, 2791, 3163 |

At $d=167$ we also test $167^x+b^4=c^{11}\pmod{23}$ directly. This condition is periodic in $x$ modulo 22 since $23\nmid167$. The complete odd-exponent enumeration is reproduced by `python3 scripts/check_twists.py --exponents`. At 2471 the verifier also tests the principal class and returns it only at residues 31 and 93. The signed $(31,31,2)$ theorem independently excludes those two residues. [Proof including varying bases](varying-base.md)

## Varying the base

The cubic certificates also give infinite families with different bases. Fix one pair $(d,p)$ from the table and let $M$ be the product of its **cubic-certificate** moduli. For $u\geq1$ coprime to $M$, $j\geq0$ and $b_0,c_0\geq1$, a primitive solution of

$$
(d\,u^{4p})^{3+4pj}+B^{4b_0}=C^{pc_0}
$$

is impossible. To verify this, put $x=3+4pj$ and $W=d^ju^x$. Then the first summand is $d^3W^{4p}$. The right base is odd by primitivity when $u$ is even and by the calculation modulo 16 when $u$ is odd. The element $B^{2b_0}+d W^{2p}s$ now has norm $C^{pc_0}$, and its conjugate ideals are coprime because $\gcd(C,2du)=1$. The same argument gives a global $k$. At each auxiliary modulus divide the local identity by $W^{2p}$, a unit that is both a square and a $p$th power. Its real term becomes $(B^{b_0}/W^p)^2$ and the coefficient of $s$ becomes $d$. This produces exactly the forbidden cubic witnesses. The step uses the same class index at every modulus.

## Relation to existing work

Taking $X=b^2$ embeds the cubic cases into $X^2+d^3=c^p$. Freitas, Naskręcki and Stoll classified the larger signature $(2,3,11)$ conditional on class group calculations under GRH. Jaswal's October 2026 preprint gives an unconditional classification at 11, 17 and 19 and explicitly leaves out 31 from its range through 36. The $d=167$, $x=3$ calculation is an independent check of a covered case. The $d=2471$ result fixes one base at exponent 31. The available comparisons do not establish priority for these deductions. [Freitas–Naskręcki–Stoll, Theorem 1.4](https://doi.org/10.1112/S0010437X19007693) · [Jaswal, Theorem A and Table 1](https://manvirjaswal.github.io/papers/x2-y3-zn/)
