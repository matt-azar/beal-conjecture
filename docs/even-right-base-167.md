# An even right base at 167

**Claim.** There are no positive integers $x,U,c$ and no prime $p\ge7$ with $x$ odd, $c$ even, $167\nmid U$ and
$$
167^x+U^2=c^p.
$$
For $p=5$ the same holds unless the 5-torsion of the Frey curve below is reducible. That exception is not excluded here.

**Status.** Derived and computed by the lead on 2026-11-27 as the first step of task R3. **Unreviewed.** No other agent has checked the argument or replayed the computation, and other work must not build on it yet. The computation was run with PARI/GP 2.15.4, not the pinned 2.17.2. Three external sources (the isogeny classification, Siksek's notes, Bennett–Siksek) could not be opened from the session that wrote this note, because its network policy blocked their hosts. The uses of them below repeat uses already on `main`, except where marked **source not reopened**. Those marks are requests to the citation check.

**Why this case.** For an arbitrary square summand, $U$ odd and $c$ even is locally possible. When $p\nmid h(-167)=11$ the class group gives no obstruction, and the primitive-divisor argument needs $c$ odd. This is the branch that the fourth power excluded by parity. At $p=11$ it is already excluded by the [class relation](frey-167.md#an-arbitrary-square-summand-at-exponent-11), and the argument here covers $p=11$ a second time by a different route.

## The Frey curve

Let $D=167^x$ and $C=c^p$, so $U^2+D=C$. Since $x$ is odd, $D\equiv7\pmod{16}$. Assume first $v_2(C)\ge7$, which holds for $p\ge7$, and for $p=5$ when $4\mid c$. Then $U^2\equiv-D\equiv9\pmod{16}$, so $U\equiv\pm3\pmod8$. Replace $U$ by $-U$ if necessary so that $U\equiv5\pmod8$. Put
$$
E:\ Y^2=X^3+UX^2+\frac C4X,\qquad \Delta=16\Big(\frac C4\Big)^2(U^2-C)=-DC^2,\qquad c_4=16\Big(U^2-\frac{3C}4\Big).
$$
The point $(0,0)$ has order 2.

*At 2.* The substitution $X=4X'$, $Y=8Y'+4X'$ gives the integral model
$$
Y'^2+X'Y'=X'^3+\frac{U-1}4X'^2+\frac C{64}X',
$$
with $c_4'=U^2-3C/4$ odd and $\Delta'=-DC^2/2^{12}$ even. So the reduction is multiplicative, the model is minimal, and $v_2(\Delta_{\min})=2p\,v_2(c)-12$. The reduced curve is $Y^2+XY=X^3+aX^2$ with $a=(U-1)/4$ odd. The tangent directions at the node are the roots of $T^2+T+1$, which are not in $\mathbb F_2$. The reduction is nonsplit and $a_2(E)=-1$.

*At 167.* $c_4\equiv16U^2$ is a unit and $v_{167}(\Delta)=x$, so the reduction is multiplicative with $v_{167}(\Delta_{\min})=x$.

*At an odd prime $\ell\mid c$.* $c_4\equiv16U^2$ is a unit, since $\gcd(U,c)=1$. The reduction is multiplicative with $v_\ell(\Delta_{\min})=2p\,v_\ell(c)$. The reduced curve is $Y^2=X^2(X+U)$, split exactly when $U$ is a square modulo $\ell$.

All other primes are good. Hence $E$ is semistable of conductor $2\cdot167\cdot\mathrm{rad}_{\text{odd}}(c)$.

The script samples the reduction at 2 over all odd $x<32$ and $U$ modulo $2^{14}$ and finds conductor exponent 1 and $a_2=-1$ in every case. This is a check of the calculation above, which does not depend on it.

## Irreducibility

A Galois-stable line in $E[p]$ together with $(0,0)$ would give a rational cyclic isogeny of degree $2p$. For $p\ge11$ no elliptic curve over $\mathbb Q$ has one. This is the classification already used on `main` for degrees 22, 26 and 62. [Cyclic isogeny classification, Theorem 2.1.48](https://grantmolnar.com/pdfs/Counting_elliptic_curves_with_a_cyclic_m_isogeny_over_Q.pdf)

For $p=7$, degree 14 does occur, but only for curves with complex multiplication, which have integral $j$-invariant. $E$ has multiplicative reduction at 2, so its $j$-invariant is not integral. **Source not reopened:** the statement that the non-cuspidal rational points of $X_0(14)$ are the two CM points $j=-3375$ and $j=16581375$ is written from memory and must be confirmed against the classification before this note counts as reviewed.

For $p=5$ this argument is not available, since $X_0(10)$ has genus 0.

## Level lowering

Assume $E[p]$ is irreducible. Level lowering, in the form used throughout the repository, removes every prime $q\parallel N_E$ with $p\mid v_q(\Delta_{\min})$. Every odd prime of $c$ is removed. The prime 2 stays, because $p\nmid2p\,v_2(c)-12$ for $p\ge5$. The prime 167 stays exactly when $p\nmid x$. So there is a newform $f$ of weight 2 and exact level 334, or exact level 2 if $p\mid x$, and a prime $\lambda\mid p$ of its coefficient field, such that for every prime $\ell\nmid 2\cdot167\cdot p$
$$
a_\ell(f)\equiv a_\ell(E)\pmod\lambda\ \text{ if }\ell\nmid c,\qquad a_\ell(f)\equiv\Big(\frac U\ell\Big)(\ell+1)\pmod\lambda\ \text{ if }\ell\mid c.
$$
[Siksek, §5.2, Theorem 3 and Proposition 5.1](https://samirsiksek.github.io/siksek.github.io/papers/ihpnotes7.pdf)

There are no newforms of level 2. So $p\nmid x$ and the level is 334. This does not use Darmon–Merel.

## Elimination at level 334

For a prime $\ell\nmid2\cdot167$ let $A_\ell$ be the set of traces $a_\ell(E_{U,D})$ over all $U$ modulo $\ell$ and all $D\equiv167^x$ with $x$ odd and $U^2+D\not\equiv0$. Put
$$
B_\ell(f)=\ell\cdot\prod_{a\in A_\ell}N(a_\ell(f)-a)\cdot N\big(a_\ell(f)^2-(\ell+1)^2\big),
$$
omitting the last factor when $-167^x$ is a non-square modulo $\ell$ for every odd $x$, in which case $\ell\nmid c$. A newform arising from a solution at exponent $p$ has $p\mid B_\ell(f)$ for every such $\ell$.

The newspace of level 334 has dimension 13 and six Galois classes.

| Class | Degree | Coefficient field | $a_2$ | $\gcd_{3\le\ell\le60}B_\ell$ |
|---:|---:|---|---:|---|
| 1 | 1 | $\mathbb Q$ | 1 | $3^2\cdot5^2$ |
| 2 | 2 | $y^2-y-1$ | 1 | 5 |
| 3 | 2 | $y^2-2$ | −1 | 1 |
| 4 | 2 | $y^2-y-1$ | −1 | 1 |
| 5 | 3 | $y^3-y^2-7y+8$ | 1 | 1 |
| 6 | 3 | $y^3-y^2-5y+4$ | −1 | $2^{10}\cdot7$ |

So for $p\ge11$ nothing survives, and for $p=7$ only class 6 does. Note that the column $a_2$ is not used for $p\ge7$.

*Class 6 at 7.* The polynomial $y^3-y^2-5y+4$ has discriminant $469=7\cdot67$, which is squarefree, so $\mathbb Z[y]$ is the maximal order. Modulo 7 it factors as $(y+1)^2(y+4)$, giving two primes $\lambda_1,\lambda_2$ with residue field $\mathbb F_7$.

| $\ell$ | $a_\ell(f)\bmod\lambda_1$ | $a_\ell(f)\bmod\lambda_2$ | Admissible residues modulo 7 |
|---:|---:|---:|---|
| 3 | 1 | 4 | 0, 3, 4 |
| 5 | 4 | 6 | 0, 2, 3, 4, 5 |

At 3, $D\equiv2$, the only good fibre is $U\equiv0$ with trace 0, and $3\mid c$ gives $\pm4$. At 5, $-167^x$ is a non-square for odd $x$, so $5\nmid c$ and the residues are the good traces $0,\pm2,\pm4$. The prime $\lambda_1$ fails at 3 and $\lambda_2$ fails at 5. Class 6 does not survive at 7. The norm in $B_\ell$ could not see this, because each of the two primes passes one of the two tests.

This proves the claim for $p\ge7$, subject to the status paragraph.

## The exponent 5

*$4\mid c$ and $E[5]$ irreducible.* The curve and the level are as above. Classes 3 to 6 are eliminated, since 5 does not divide their entries in the table. Classes 1 and 2 have $a_2(f)=1$. The prime 2 divides both $N_E$ and the level exactly once, and comparing the two unramified characters on a decomposition group at 2 gives $a_2(f)\equiv a_2(E)=-1\pmod\lambda$ for $p\ge5$. So $2\in\lambda$, impossible. **Source not reopened:** this comparison at a prime dividing the lowered level is standard, but no source for it has been checked.

*$v_2(c)=1$ and $E[5]$ irreducible.* Now $v_2(C)=5$ and the model above is not integral. For $U\equiv1\pmod4$ the script finds Kodaira type III and conductor exponent 3 at 2 for $Y^2=X^3+UX^2+(C/4)X$ in every sampled class. This is a computation over samples and not yet a derivation by Tate's algorithm. The odd primes are as before, and the lowered level is $8\cdot167=1336$. Its newspace has dimension 42 and five classes, of degrees 2, 7, 9, 12, 12. The gcd of $B_\ell$ over $3\le\ell\le60$ is $5$, $1$, $1$, $2^{16}$, $2^{14}$. Class 1 has field $\mathbb Q(\sqrt5)$ and one prime $\lambda$ above 5. At $\ell=41\equiv1\pmod5$, where $C$ must be a fifth power, the admissible residues are $\{2,3\}$ and $a_{41}(f)\equiv0\pmod\lambda$. So nothing survives.

*$E[5]$ reducible.* Not excluded. A local sieve on $x$ (requiring $a_\ell(E)\equiv\ell+1\pmod5$ at good primes) removes only some residue classes of $x$, at 17 and 101 among primes below 400, and was not pursued. This is an exploratory observation with no script in the repository.

## Consequence for R3, and what remains

Suppose the claim survives review. For $167^x+U^2=c^z$ with $167\nmid U$:

- $x$ even is in the literature (Bennett–Siksek, Theorem 4, as recorded in the [audit](audit.md#what-is-new)).
- $x$ odd, $c$ odd, and a prime $p\ge5$ dividing $z$: $p=11$ is the [Frey proof](frey-167.md#an-arbitrary-square-summand-at-exponent-11). For $p\ne11$ the primitive-divisor step of the [audit skeleton](audit.md#skeleton) applies. It is written there for $U=b^2$, but uses only that $c$ is odd and prime to $U$.
- $x$ odd, $c$ even, and a prime $p\ge7$ dividing $z$: this note.

That would leave, for base 167 and $y$ even, exactly these branches:

1. $z$ a power of 2.
2. $3\mid z$: points on $Y^2=X^3-167^r$.
3. $5\mid z$ with $x$ odd, $c$ even and $E[5]$ reducible.

Whether the published literature already contains the claim for $q=167$ has not been checked. Bennett–Siksek treat this branch for primes $q<100$. The method here is the standard one, and the claim is at most a new instance.

## Computation

```sh
gp -q -f scripts/check_even_base_167.gp < /dev/null
```

Output with PARI/GP 2.15.4, apart from a stack-size warning:

```
== Reduction at 2, sampled over odd x < 32 and U mod 2^14 ==
v_2(C) >= 7, U = 1 mod 4: [U mod 8, conductor exponent, a_2] in [[5, 1, -1]]
v_2(C) = 5, U = 1 mod 4: [conductor exponent, Kodaira code] in [[3, -3]]
== Level 334 ==
level 334: newspace dimension 13, 6 Galois classes
  class 1: degree 1, field y, a_2 = 1, gcd of B_l for 3 <= l <= 60: [3, 2; 5, 2]
  class 2: degree 2, field y^2 - y - 1, a_2 = 1, gcd of B_l for 3 <= l <= 60: Mat([5, 1])
  class 3: degree 2, field y^2 - 2, a_2 = -1, gcd of B_l for 3 <= l <= 60: matrix(0,2)
  class 4: degree 2, field y^2 - y - 1, a_2 = -1, gcd of B_l for 3 <= l <= 60: matrix(0,2)
  class 5: degree 3, field y^3 - y^2 - 7*y + 8, a_2 = 1, gcd of B_l for 3 <= l <= 60: matrix(0,2)
  class 6: degree 3, field y^3 - y^2 - 5*y + 4, a_2 = -1, gcd of B_l for 3 <= l <= 60: [2, 10; 7, 1]
class 6 at 7:
  l = 3: a_l(f) at the primes [Mod(1, 7)*y + Mod(1, 7), Mod(1, 7)*y + Mod(4, 7)] with exponents [2, 1] is [Mod(1, 7), Mod(4, 7)], admissible residues mod 7: [0, 3, 4]
  l = 5: a_l(f) at the primes [Mod(1, 7)*y + Mod(1, 7), Mod(1, 7)*y + Mod(4, 7)] with exponents [2, 1] is [Mod(4, 7), Mod(6, 7)], admissible residues mod 7: [0, 2, 3, 4, 5]
== Level 1336 (p = 5 and v_2(c) = 1) ==
level 1336: newspace dimension 42, 5 Galois classes
  class 1: degree 2, field y^2 - y - 1, a_2 = 0, gcd of B_l for 3 <= l <= 60: Mat([5, 1])
  class 2: degree 7, ..., gcd of B_l for 3 <= l <= 60: matrix(0,2)
  class 3: degree 9, ..., gcd of B_l for 3 <= l <= 60: matrix(0,2)
  class 4: degree 12, ..., gcd of B_l for 3 <= l <= 60: Mat([2, 16])
  class 5: degree 12, ..., gcd of B_l for 3 <= l <= 60: Mat([2, 14])
class 1 at 5:
  l = 41: a_l(f) at the primes [Mod(1, 5)*y + Mod(2, 5)] with exponents [2] is [Mod(0, 5)], admissible residues mod 5: [2, 3]
== Positive control: 7 + 11^2 = 2^7, level 14 ==
level 14: newspace dimension 1, 1 Galois classes
  class 1: degree 1, field y, a_2 = -1, gcd of B_l for 3 <= l <= 60: 0
  Frey curve of the control: conductor 14, a_2 = -1, traces agree with the newform for 3 <= l <= 60: 1
```

`matrix(0,2)` is PARI's factorization of 1. The three lines with `...` are abbreviated here: the script prints the defining polynomials of the fields.

**Positive control.** $7+11^2=2^7$ is a genuine solution of the same shape with base 7. Its Frey curve, with $U=-11\equiv5\pmod8$, has conductor 14 and $a_2=-1$, and the same sieve code returns $\gcd B_\ell=0$ for the newform of level 14. So the sieve does not eliminate a form that comes from a solution.

## For the reviewer

Things most likely to be wrong, in the lead's own estimate:

1. The trace sets $A_\ell$. They must contain every trace a solution can produce. They are taken over all $U$ modulo $\ell$ and all odd $x$, with no $p$th-power condition except in the two per-prime tables.
2. The sign of the multiplicative trace, $(U/\ell)$. The elimination of $\lambda_1$ at 3 does not depend on it, since neither sign gives residue 1.
3. The normalization $U\equiv5\pmod8$, and whether the curve for $-U$ needs separate treatment. It is the quadratic twist by $-1$ and is not used.
4. The three items marked **source not reopened**, and the sampled conductor at 2 for $v_2(c)=1$.
5. The case $\ell=p$. The factor $\ell$ in $B_\ell$ handles it for the gcd column. The per-prime tables use $\ell=3,5$ for $p=7$ and $\ell=41$ for $p=5$.
