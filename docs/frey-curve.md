# A single modular-form level for the exponent-31 family

Suppose $d^x+b^4=c^{31}$ is primitive, with $d=2471=7\cdot353$ and odd $x\geq3$. The [class-group descent](descent.md) gives $x\equiv5\pmod{62}$. Such a solution would produce a weight-two newform of **exact level 79072 with nonrational coefficients**. The modularity and level-lowering inputs below are published theorems. The exclusion of the rational forms is a table calculation. The simultaneous Hecke calculation below eliminates the forms in every coefficient field.

## Conductor and level

Since $d\equiv7\pmod{16}$, an odd $b$ would force $c$ even and $c^{31}\equiv8\pmod{16}$, which is impossible. Thus $b$ is even and $c^{31}\equiv7\pmod{16}$. Set
$$
E:\quad Y^2=X^3+2b^2X^2+c^{31}X.
$$
Its invariants are $\Delta=-64 d^x c^{62}$ and $c_4=16(b^4-3d^x)$. Primitivity gives $\gcd(d,c)=\gcd(b,c)=1$. At each odd $q\mid dc$, $c_4$ is a unit, so the model is minimal and has multiplicative reduction. At $q\mid d$ the special fiber is $Y^2=X(X+b^2)^2$. Its tangent slopes at the node are $\pm b\sqrt{-1}$, giving nonsplit reduction at 7 and split reduction at 353. At $q\mid c$, the slopes at zero are $\pm b\sqrt{2}$.

At 2 the displayed integral model is minimal since $v_2(\Delta)=6<12$. Translate $X$ by 1 to put the singular point at the origin. The coefficients become $a_2'=3+2b^2$, $a_4'=3+4b^2+c^{31}\equiv2\pmod4$, $a_6'=1+2b^2+c^{31}\equiv0\pmod8$, and $a_1'=a_3'=0$. Thus $b_8'=4a_2'a_6'-(a_4')^2\equiv4\pmod8$. Tate's algorithm gives type III and conductor exponent $v_2(\Delta)-1=5$. All remaining primes have good reduction. [Tate's algorithm, step 4](https://research.vu.nl/ws/portalfiles/portal/149169942/J%20M%20%20van%20Langen%20-%20thesis.pdf)

It follows that $N_E=2^5d\,\mathrm{rad}(c)$. Mazur's prime-isogeny theorem excludes a rational 31-isogeny for every elliptic curve over $\mathbb Q$, so $E[31]$ is irreducible. Apply Siksek's Theorem 3 with $p=31$. It supplies a normalized newform in $S_2(\Gamma_0(N_p))$ of exact level $N_p$, obtained by deleting from $N_E$ the primes $q$ with $q\parallel N_E$ and $p\mid v_q(\Delta_{\min})$. Every $q\mid c$ satisfies this condition, including $q=31$ if it divides $c$. At $7,353$ the discriminant valuation is $x\equiv5\pmod{31}$, and $2^5\parallel N_E$ leaves 2 outside the deletion rule. Hence $N_p=2^5\cdot7\cdot353=79072$. This exact-level conclusion uses the stated weight-two theorem, not an upper bound on a conductor. [Mazur, Theorem 1](https://www.math.columbia.edu/~goldfeld/Mazur-Goldfeld1978.pdf) · [Siksek, §5.2, equation (2) and Theorem 3](https://samirsiksek.github.io/siksek.github.io/papers/ihpnotes7.pdf)

## Elimination at 5

As $d\equiv1\pmod5$, one has $c^{31}\equiv b^4+1\in\{1,2\}\pmod5$. Thus $E$ has good reduction there. Counting points over $\mathbb F_5$ gives $a_5(E)=2$ when $5\mid b$ and $a_5(E)=-2$ otherwise. Every candidate newform must satisfy $a_5(f)\equiv\pm2\pmod{\lambda}$ at some prime $\lambda\mid31$ of its coefficient field.

By modularity and Eichler–Shimura the rational newforms correspond to elliptic-curve isogeny classes of that conductor. The complete Cremona table gives two. Both have $a_5=-1$, which eliminates them. [Table completeness](https://www.lmfdb.org/knowledge/show/rcs.cande.ec.q) · [Mathematical and computational dependencies](https://www.lmfdb.org/knowledge/show/rcs.rigor.ec.q)

| Cremona class | Representative | $a_5$ | $a_{683}$ |
|---|---|---:|---:|
| 79072a | $Y^2=X^3+37X+114$ | −1 | −4 |
| 79072b | $Y^2=X^3+37X-114$ | −1 | 4 |

The degree-one exclusion can be reproduced from the repository root. The script checks the hash before enumerating the rows and counting points.

```sh
curl -fL https://raw.githubusercontent.com/JohnCremona/ecdata/6fedd3ab463a70e52061ebc0b04832ad19fd2e01/curves/curves.70000-79999 -o /tmp/curves.70000-79999
python3 scripts/check_frey.py /tmp/curves.70000-79999
```

## The second trace and the contradiction

The global twist imposes a second constraint. At $q=683$, substituting both roots of $s^2=-d$ as in the descent leaves $b\equiv\pm26$ for $(x,k)=(5,23)$ and $b\equiv\pm298$ for $(67,8)$, with the exponents here taken at their representatives modulo 124. For each such $b$, $b^4+d^x\equiv0\pmod{683}$. Increasing $x$ by 124 rescales $b$ by $d^{31}$, a unit at 683, so $683\mid c$ for every putative solution in either class. Because $683\equiv3\pmod8$, 2 is a nonsquare, giving nonsplit multiplicative reduction there. On the semisimplified residual representation the Frobenius eigenvalues are $-1,-683$ (the unramified quadratic twist of the Tate curve). At the lowered level, $683$ is good, hence $a_{683}(f)\equiv-(683+1)\equiv-2\pmod\lambda$. [Local representations at multiplicative primes, §5](https://samirsiksek.github.io/siksek.github.io/papers/ihpnotes7.pdf)

The exact-level newspace has dimension 2112 by PARI/GP. In the quaternionic realization the full Brandt module has dimension 8496. On this module $T_5^2+T_{683}-2I$ has determinant $29$ modulo 31. A form satisfying the required traces would give an eigenvalue congruent to $4-2-2=0$, impossible. Classical modular symbols independently give full column rank for both simultaneous systems. Hence no primitive solution exists for odd $x\geq3$. [Quaternionic computation and proof](brandt-sieve.md) · [Classical verifier](../scripts/check_eclib_hecke.cpp) · [All right exponents](fixed-bases.md)
